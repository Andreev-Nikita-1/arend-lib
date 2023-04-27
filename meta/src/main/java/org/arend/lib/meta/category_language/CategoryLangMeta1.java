package org.arend.lib.meta.category_language;

import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.definition.FunctionKind;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.*;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.arend.lib.util.Values;
import org.arend.term.concrete.Concrete;
import org.arend.term.concrete.SubstConcreteVisitor;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class CategoryLangMeta1 extends BaseMetaDefinition {
    private ConcreteFactory fac;
    ExpressionTypechecker typechecker;
    ConcreteSourceNode marker;
    private final StdExtension ext;
    public FieldsProvider fp = new FieldsProvider();

    public CategoryLangMeta1(StdExtension ext) {
        this.ext = ext;
    }

    @Override
    public boolean[] argumentExplicitness() {
        return new boolean[]{true};
    }

    public boolean compare(CoreExpression value, CoreExpression element) {
        if (value == null || element == null) return value == element;
        return typechecker != null ? Utils.safeCompare(typechecker, value, element, CMP.EQ, marker, false, true, true) : value.compare(element, CMP.EQ);
    }

    private List<Pair<CoreExpression, ArendRef>> refs;

    private ArendRef getRef(CoreReferenceExpression expr) {
        for (var x : refs) {
            if (compare(x.proj1, expr)) {
                return x.proj2;
            }
        }
        return null;
    }

    private Values<CoreReferenceExpression> typesParameters;

    private void addTypeParam(CoreReferenceExpression param) {
        typesParameters.addValue(param);
        refs.add(new Pair<>(param, fac.local(param.getBinding().getName())));
    }

    private List<Pair<Pair<CoreExpression, CoreExpression>, Values<CoreReferenceExpression>>> termsParameters;

    private void addTermParam(CoreExpression dom, CoreExpression cod, CoreReferenceExpression param) {
        var v = termsParameters.stream()
                .filter(x -> compare(x.proj1.proj1, dom) && compare(x.proj1.proj2, cod))
                .map(x -> x.proj2).collect(Collectors.toList());
        if (v.size() == 0) {
            var values = new Values<CoreReferenceExpression>(typechecker, marker);
            values.addValue(param);
            termsParameters.add(new Pair<>(new Pair<>(dom, cod), values));
        } else {
            v.get(0).addValue(param);
        }
        refs.add(new Pair<>(param, fac.local(param.getBinding().getName())));
    }

    private int findTermNumber(CoreExpression dom, CoreExpression cod, CoreReferenceExpression param) {
        var v = termsParameters.stream()
                .filter(x -> compare(x.proj1.proj1, dom) && compare(x.proj1.proj2, cod))
                .map(x -> x.proj2).collect(Collectors.toList());
        if (v.size() > 0) {
            return v.get(0).getIndex(param);
        }
        return -1;
    }

    private List<Pair<CoreExpression, Values<CoreReferenceExpression>>> predicateParameters;

    private void addPredicateParam(CoreExpression dom, CoreReferenceExpression param) {
        var v = predicateParameters.stream()
                .filter(x -> compare(x.proj1, dom))
                .map(x -> x.proj2).collect(Collectors.toList());
        if (v.size() == 0) {
            var values = new Values<CoreReferenceExpression>(typechecker, marker);
            values.addValue(param);
            predicateParameters.add(new Pair<>(dom, values));
        } else {
            v.get(0).addValue(param);
        }
        refs.add(new Pair<>(param, fac.local(param.getBinding().getName())));
    }

    private int findPredicateNumber(CoreExpression dom, CoreReferenceExpression param) {
        var v = predicateParameters.stream()
                .filter(x -> compare(x.proj1, dom))
                .map(x -> x.proj2).collect(Collectors.toList());
        if (v.size() > 0) {
            return v.get(0).getIndex(param);
        }
        return -1;
    }

    private List<Pair<Pair<CoreExpression, Pair<CoreExpression, CoreExpression>>, Values<CoreReferenceExpression>>> hypothesisParameters;

    private void addHypothesisParam(CoreExpression dom, CoreExpression hyp, CoreExpression form, CoreReferenceExpression param) {
        var v = hypothesisParameters.stream()
                .filter(x -> compare(x.proj1.proj1, dom) && compare(x.proj1.proj2.proj1, hyp)
                        && compare(x.proj1.proj2.proj2, form))
                .map(x -> x.proj2).collect(Collectors.toList());
        if (v.size() == 0) {
            var values = new Values<CoreReferenceExpression>(typechecker, marker);
            values.addValue(param);
            hypothesisParameters.add(new Pair<>(new Pair<>(dom, new Pair<>(hyp, form)), values));
        } else {
            v.get(0).addValue(param);
        }
        refs.add(new Pair<>(param, fac.local(param.getBinding().getName())));
    }

    private Pair<Pair<CoreExpression, Pair<CoreExpression, CoreExpression>>, Values<CoreReferenceExpression>> findHypothesis(CoreReferenceExpression param) {
        for (var x : hypothesisParameters) {
            if (x.proj2.getIndex(param) != -1) {
                return x;
            }
        }
        return null;
    }

    @Dependency(module = "CategoryLanguage.Util", name = "sigma")
    private CoreFunctionDefinition sigma;
    @Dependency(module = "CategoryLanguage.Util", name = "wrapType")
    private CoreFunctionDefinition wrapType;


    private boolean isType(CoreExpression expr) {
        if (expr instanceof CoreSigmaExpression) {
            var link = ((CoreSigmaExpression) expr).getParameters();
            try {
                link.getBinding().getName();
            } catch (IllegalStateException e) {
                return true;
            }
            List<CoreBinding> bindings = new ArrayList<>();
            while (link.hasNext()) {
                bindings.add(link.getBinding());
                link = link.getNext();
            }
            boolean res = isType(bindings.get(bindings.size() - 1).getTypeExpr());
            for (int i = bindings.size() - 2; i >= 0; i--) {
                var cur = isType(bindings.get(i).getTypeExpr());
                res = cur && res;
            }
            return res;
        }
        if (expr instanceof CoreReferenceExpression) { // TParam
            return (typesParameters.getIndex(expr) != -1);
        }
        return false;
    }

    private CoreExpression wrapType(CoreExpression type) {
        return typechecker.typecheck(fac.app(fac.ref(wrapType.getRef()), fac.arg(fac.core(type.computeTyped()), true)), null).getExpression();
    }

    private void parse(CoreParameter parameter) {
        var type = parameter.getTypeExpr();
        var ref = parameter.getBinding().makeReference();
        if (type instanceof CoreUniverseExpression) { // type parameter
            addTypeParam(ref);
        } else if (type instanceof CorePiExpression typePi) { // functional symbol or predicate or hypothesis
            var codomain = typePi.getCodomain();
            if (codomain instanceof CoreUniverseExpression) { // predicate parameter
                var domain = typePi.getParameters().getTypeExpr();
                addPredicateParam(domain, ref);
            } else if (isType(codomain)) { // functional symbol
                addTermParam(typePi.getParameters().getTypeExpr(), codomain, ref);
            } else if (codomain instanceof CorePiExpression codomainPi) { // hypothesis with hyp and form
                var domain = typePi.getParameters().getTypeExpr();
                var hyp = codomainPi.getParameters().getTypeExpr();
                var form = codomainPi.getCodomain();
                addHypothesisParam(domain, hyp, form, ref);
            } else if (isType(typePi.getParameters().getTypeExpr())) { // hypothesis as just formula
                var domain = typePi.getParameters().getTypeExpr();
                addHypothesisParam(domain, wrapType(domain), codomain, ref);
            } else { // hypothesis with hyp and form without context
                var hyp = typePi.getParameters().getTypeExpr();
                var form = typePi.getCodomain();
                addHypothesisParam(sigma.getResultType(), hyp, form, ref);
            }
        } else if (isType(type)) { // constant symbol
            addTermParam(sigma.getResultType(), type, ref);
        } else { // hypothesis as just formula without context
            addHypothesisParam(sigma.getResultType(), wrapType(sigma.getResultType()), type, ref);
        }
    }

    private CoreExpression parseArgs(CoreExpression lam, int proofStart) {
        if (lam instanceof CoreLamExpression && proofStart > 0) {
            var params = ((CoreLamExpression) lam).getParameters();
            while (params.hasNext()) {
                proofStart--;
                parse(params);
                params = params.getNext();
            }
            return parseArgs(((CoreLamExpression) lam).getBody(), proofStart);
        }
        return lam;
    }


    private ConcreteExpression listMap(List<? extends ConcreteExpression> args) {
        var res = fac.app(fac.ref(ext.nil.getRef()));
        for (int i = args.size() - 1; i >= 0; i--) {
            var res1 = fac.app(fac.ref(ext.cons.getRef()),
                    fac.arg(args.get(i), true));
            res = fac.app(res1, fac.arg(res, true));
        }
        return fac.app(fac.ref(ext.at.getRef()), fac.arg(res, true));
    }

    private ConcreteExpression constructTypeLets(ConcreteExpression expr) {

        var TPterm = fac.app(fac.ref(ext.prelude.getFin().getRef()),
                fac.arg(fac.number(typesParameters.getValues().size()), true));
        var TPclause = fac.letClause(fac.refPattern(fp.TP, null), null, TPterm);

        var TyFterm = listMap(typesParameters.getValues().stream().map(x -> fac.ref(getRef(x)))
                .collect(Collectors.toList()));
        var TyFclause = fac.letClause(fac.refPattern(fp.TyF, null), null, TyFterm);

        return fac.letExpr(false, false, List.of(TPclause, TyFclause), expr);
    }


    private FieldsProvider.ExpressionAndPattern constructType(CoreExpression expr) {
        if (expr instanceof CoreInferenceReferenceExpression expr1) {
            expr = expr1.getSubstExpression();
        }
        if (expr instanceof CoreSigmaExpression) { // Unit or Prod
            var link = ((CoreSigmaExpression) expr).getParameters();
            try {
                link.getBinding().getName();
            } catch (IllegalStateException e) {
                return fp.unitT();
            }
            List<CoreBinding> bindings = new ArrayList<>();
            while (link.hasNext()) {
                bindings.add(link.getBinding());
                link = link.getNext();
            }
            var res = constructType(bindings.get(bindings.size() - 1).getTypeExpr());
            for (int i = bindings.size() - 2; i >= 0; i--) {
                var cur = constructType(bindings.get(i).getTypeExpr());
                res = fp.prodT(cur, res);
            }
            return res;
        }
        if (expr instanceof CoreReferenceExpression) { // TParam
            return fp.paramT(typesParameters.getIndex(expr));
        }
        return null;
    }

    private FieldsProvider.ExpressionAndPattern constructTerm(CoreExpression expr, CoreExpression ctx) {
        return constructTerm(expr, ctx, new ArrayList<>());
    }

    private FieldsProvider.ExpressionAndPattern constructTerm(CoreExpression expr, CoreExpression ctx, List<ArendRef> pathsRefs) {
        if (expr instanceof CoreInferenceReferenceExpression) {
            expr = ((CoreInferenceReferenceExpression) expr).getSubstExpression();
        }
        if (expr instanceof CoreAppExpression) { // Param
            var fun = ((CoreAppExpression) expr).getFunction();
            var arg = ((CoreAppExpression) expr).getArgument();
            var type = fun.computeType();
            if (type instanceof CorePiExpression) {
                var dom = ((CorePiExpression) type).getParameters().getTypeExpr();
                var cod = ((CorePiExpression) type).getCodomain();
                if (fun instanceof CoreReferenceExpression funRef)
                    return fp.param(constructTerm(arg, ctx, pathsRefs), constructType(cod), constructType(dom),
                            findTermNumber(dom, cod, funRef), pathsRefs);
            }
        } // Parameter
        if (expr instanceof CoreReferenceExpression) { // Var or constant
            var type = expr.computeType();
            if (findTermNumber(sigma.getResultType(), type, (CoreReferenceExpression) expr) != -1) { // constant
                return fp.param(fp.unit(constructType(ctx), pathsRefs), constructType(type), fp.unitT(),
                        findTermNumber(sigma.getResultType(), type, (CoreReferenceExpression) expr), pathsRefs);
            }
            return fp.var(constructType(type), pathsRefs);
        } // Var or constant
        if (expr instanceof CoreTupleExpression) { // unit or Tuple
            var fields = ((CoreTupleExpression) expr).getFields();
            if (fields.size() == 0) {
                return fp.unit(constructType(ctx), pathsRefs);
            }
            var res = constructTerm(fields.get(fields.size() - 1), ctx, pathsRefs);
            var resType = constructType(fields.get(fields.size() - 1).computeType());
            for (int i = fields.size() - 2; i >= 0; i--) {
                var cur = constructTerm(fields.get(i), ctx, pathsRefs);
                var curType = constructType(fields.get(i).computeType());

                res = fp.tuple(cur, res, curType, resType, pathsRefs);
                resType = fp.prodT(curType, resType);
            }
            return res;
        } // unit or Tuple
        if (expr instanceof CoreProjExpression) { // Proj
            var type = ((CoreProjExpression) expr).getExpression().computeType();
            var link = ((CoreSigmaExpression) type).getParameters();
            List<FieldsProvider.ExpressionAndPattern> types = new ArrayList<>();
            int n = 0;
            while (link.hasNext()) {
                types.add(constructType(link.getTypeExpr()));
                n++;
                link = link.getNext();
            }
            List<FieldsProvider.ExpressionAndPattern> typesCumulative = new ArrayList<>();
            FieldsProvider.ExpressionAndPattern cur = types.get(types.size() - 1);
            typesCumulative.add(cur);
            for (int i = types.size() - 2; i >= 0; i--) {
                typesCumulative.add(fp.prodT(types.get(i), cur));
                cur = fp.prodT(types.get(i), cur);
            }

            var term = constructTerm(((CoreProjExpression) expr).getExpression(), ctx, pathsRefs);

            int ind = ((CoreProjExpression) expr).getField();
            boolean last = n == ind + 1;
            int Sind = 0;
            while (ind > 0) {
                term = fp.proj2(types.get(Sind++), term, pathsRefs);
                ind--;
            }
            return last ? term : fp.proj1(typesCumulative.get(typesCumulative.size() - 1 - (Sind + 1)), term, pathsRefs);
        } // Proj
        return null;
    }

    private FieldsProvider.ExpressionAndPattern constructFormula(CoreExpression expr, CoreExpression ctx) {
        return constructFormula(expr, ctx, new ArrayList<>());
    }

    private FieldsProvider.ExpressionAndPattern constructFormula(CoreExpression expr, CoreExpression ctx, List<ArendRef> pathsRefs) {
        if (expr instanceof CoreSigmaExpression) { // conjunction
            var link = ((CoreSigmaExpression) expr).getParameters();
            try {
                link.getBinding().getName();
            } catch (IllegalStateException e) {
            }
            List<CoreBinding> bindings = new ArrayList<>();
            while (link.hasNext()) {
                bindings.add(link.getBinding());
                link = link.getNext();
            }
            var res = constructFormula(bindings.get(bindings.size() - 1).getTypeExpr(), ctx, pathsRefs);
            for (int i = bindings.size() - 2; i >= 0; i--) {
                var cur = constructFormula(bindings.get(i).getTypeExpr(), ctx, pathsRefs);
                res = fp.conj(cur, res);
            }
            return res;
        }
        if (expr instanceof CoreFunCallExpression) {
            if (((CoreFunCallExpression) expr).getDefinition() == ext.prelude.getEquality()) { //equality
                var eq = Utils.toEquality(expr, typechecker.getErrorReporter(), marker);
                var a = eq.getDefCallArguments().get(1);
                var b = eq.getDefCallArguments().get(2);
                var T = a.computeType();
                return fp.Eq(constructTerm(a, ctx, pathsRefs), constructTerm(b, ctx, pathsRefs), constructType(T));
            }
            if (((CoreFunCallExpression) expr).getDefinition() == wrapType) { //FTrue
                var type = ((CoreFunCallExpression) expr).getDefCallArguments().get(0);
                return fp.ftrue(constructType(type));
            }
        }

        if (expr instanceof CoreAppExpression) { // Param
            var fun = ((CoreAppExpression) expr).getFunction();
            var arg = ((CoreAppExpression) expr).getArgument();
            var type = fun.computeType();
            if (type instanceof CorePiExpression) {
                if (fun instanceof CoreReferenceExpression funRef) {
                    var dom1 = ((CorePiExpression) type).getParameters().getTypeExpr();
                    return fp.fparam(findPredicateNumber(dom1, funRef), constructTerm(arg, ctx, pathsRefs), constructType(dom1));
                }
            }
        }
        return null;
    }

    private ConcreteExpression constructTermlam(boolean onlySet) {
        List<ConcreteClause> clauses = new ArrayList<>();
        var all = termsParameters;
        for (var p : all) {
            var domExpr = p.proj1.proj1;
            var codExpr = p.proj1.proj2;
            var params = p.proj2;
            var domPat = constructType(domExpr).pattern;
            var codPat = constructType(codExpr).pattern;

            ConcreteClause clause;
            if (onlySet) {
                clause = fac.clause(List.of(domPat, codPat),
                        fac.app(fac.ref(ext.prelude.getFin().getRef()),
                                fac.arg(fac.number(params.getValues().size()), true)));
            } else {
                var nLocal = fac.local("n");
                var args = params.getValues().stream()
                        .map(x -> fac.ref(getRef(x))).collect(Collectors.toList());
                clause = fac.clause(List.of(domPat, codPat, fac.refPattern(nLocal, null)),
                        fac.app(listMap(args), fac.arg(fac.ref(nLocal), true)));
            }
            clauses.add(clause);
        }
        if (onlySet) clauses.add(fac.clause(List.of(fac.refPattern(null, null), fac.refPattern(null, null)),
                fac.app(fac.ref(ext.Empty.getRef()))));

        var domLocal = fac.local("dom");
        var codLocal = fac.local("cod");
        ArendRef nLocal = null;
        if (!onlySet) nLocal = fac.local("n");

        var caseArgs = onlySet ? List.of(fac.caseArg(fac.ref(domLocal), null),
                fac.caseArg(fac.ref(codLocal), null)) :
                List.of(fac.caseArg(fac.ref(domLocal), null), fac.caseArg(fac.ref(codLocal), null),
                        fac.caseArg(fac.ref(nLocal), null));
        var caseExpr = fac.caseExpr(false,
                caseArgs, null, null, clauses);
        var lamArgs = onlySet ? Arrays.asList(fac.param(domLocal), fac.param(codLocal)) :
                Arrays.asList(fac.param(domLocal), fac.param(codLocal), fac.param(nLocal));
        return fac.lam(lamArgs, caseExpr);
    }

    private ConcreteExpression constructPredicateLam(boolean onlySet) {
        List<ConcreteClause> clauses = new ArrayList<>();
        var all = predicateParameters;
        for (var p : all) {
            var domExpr = p.proj1;
            var params = p.proj2;
            var domPat = constructType(domExpr).pattern;

            ConcreteClause clause;
            if (onlySet) {
                clause = fac.clause(List.of(domPat),
                        fac.app(fac.ref(ext.prelude.getFin().getRef()),
                                fac.arg(fac.number(params.getValues().size()), true)));
            } else {
                var nLocal = fac.local("n");
                var args = params.getValues().stream()
                        .map(x -> fac.ref(getRef(x))).collect(Collectors.toList());
                clause = fac.clause(List.of(domPat, fac.refPattern(nLocal, null)),
                        fac.app(listMap(args), fac.arg(fac.ref(nLocal), true)));
            }
            clauses.add(clause);
        }
        if (onlySet) clauses.add(fac.clause(List.of(fac.refPattern(null, null)),
                fac.app(fac.ref(ext.Empty.getRef()))));

        var domLocal = fac.local("dom");
        ArendRef nLocal = null;
        if (!onlySet) nLocal = fac.local("n");

        var caseArgs = onlySet ? List.of(fac.caseArg(fac.ref(domLocal), null)) :
                List.of(fac.caseArg(fac.ref(domLocal), null),
                        fac.caseArg(fac.ref(nLocal), null));
        var caseExpr = fac.caseExpr(false,
                caseArgs, null, null, clauses);
        var lamArgs = onlySet ? List.of(fac.param(domLocal)) :
                Arrays.asList(fac.param(domLocal), fac.param(nLocal));
        return fac.lam(lamArgs, caseExpr);
    }


    @Dependency(module = "CategoryLanguage.Util", name = "Ih")
    private CoreFunctionDefinition Ih;

    @Dependency(module = "CategoryLanguage.Util", name = "Isub")
    private CoreFunctionDefinition Isub;


    private ConcreteExpression constructTermPredLets(ConcreteExpression expr) {

        var typeType = fac.app(fac.ref(fp.Type.getRef()), fac.arg(fac.ref(fp.TP), true));

        var Plam = constructTermlam(true);
        var TeFlam = constructTermlam(false);

        var PlamType = fac.pi(List.of(fac.param(true, List.of(fac.local("dom")), typeType),
                fac.param(true, List.of(fac.local("cod")), typeType)), fac.universe(null, fac.numLevel(0)));

        var domLocal = fac.local("dom");
        var codLocal = fac.local("cod");
        var nLocal = fac.local("n");
        var nType = fac.app(fac.app(fac.ref(fp.P), fac.arg(fac.ref(domLocal), true)),
                fac.arg(fac.ref(codLocal), true));
        var TeFcodomain = fac.app(fac.app(fac.app(fac.ref(Ih.getRef()),
                                fac.arg(fac.ref(fp.TyF), true)),
                        fac.arg(fac.ref(domLocal), true)),
                fac.arg(fac.ref(codLocal), true));
        var TeFlamType = fac.pi(List.of(fac.param(true, List.of(domLocal), typeType),
                        fac.param(true, List.of(codLocal), typeType), fac.param(true, List.of(nLocal), nType)),
                TeFcodomain);

        var Pclause = fac.letClause(fac.refPattern(fp.P, null), PlamType, Plam);
        var TeFclause = fac.letClause(fac.refPattern(fp.TeF, null), TeFlamType, TeFlam);


        var FPlam = constructPredicateLam(true);
        var FFlam = constructPredicateLam(false);

        var FPlamType = fac.pi(List.of(fac.param(true, List.of(fac.local("dom")), typeType)), fac.universe(null, fac.numLevel(0)));

        var domLocal1 = fac.local("dom");
        var nLocal1 = fac.local("n");
        var nType1 = fac.app(fac.app(fac.ref(fp.FP), fac.arg(fac.ref(domLocal1), true)));
        var FFcodomain = fac.app(fac.app(fac.app(fac.ref(Isub.getRef()),
                        fac.arg(fac.ref(fp.TyF), true)),
                fac.arg(fac.ref(domLocal1), true)));
        var FFlamType = fac.pi(List.of(fac.param(true, List.of(domLocal1), typeType), fac.param(true, List.of(nLocal1), nType1)),
                FFcodomain);

        var FPclause = fac.letClause(fac.refPattern(fp.FP, null), FPlamType, FPlam);
        var FFclause = fac.letClause(fac.refPattern(fp.FF, null), FFlamType, FFlam);


        return fac.letExpr(false, false, List.of(Pclause, TeFclause, FPclause, FFclause), expr);
    }

    @Dependency(module = "CategoryLanguage.Util", name = "type-is-set")
    private CoreFunctionDefinition TypeIsSet;
    @Dependency(module = "CategoryLanguage.Util", name = "rewriteFunc")
    private CoreFunctionDefinition RewriteFunc;

    private ConcreteExpression constructHypothesislam(boolean onlySet) {
        List<ConcreteClause> clauses = new ArrayList<>();
        var all = hypothesisParameters;
        for (var p : all) {
            var domExpr = p.proj1.proj1;
            var hyp = p.proj1.proj2.proj1;
            var form = p.proj1.proj2.proj2;
            var params = p.proj2;
            var domPat = constructType(domExpr).pattern;
            ArrayList<ArendRef> pathRefs = new ArrayList<>();
            var hypPat = constructFormula(hyp, domExpr, pathRefs).pattern;
            var formPat = constructFormula(form, domExpr, pathRefs).pattern;

            ConcreteClause clause;
            if (onlySet) {
                clause = fac.clause(List.of(domPat, hypPat, formPat),
                        fac.app(fac.ref(ext.prelude.getFin().getRef()),
                                fac.arg(fac.number(params.getValues().size()), true)));
            } else {
                var nLocal = fac.local("n");
                var args = params.getValues().stream()
                        .map(x -> fac.ref(getRef(x))).collect(Collectors.toList());
                var res = fac.app(listMap(args), fac.arg(fac.ref(nLocal), true));
                for (var path : pathRefs) {
                    var idpEq = fac.app(fac.ref(TypeIsSet.getRef()), fac.arg(fac.ref(path), true));
                    res = fac.app(fac.ref(RewriteFunc.getRef()), fac.arg(idpEq, true), fac.arg(res, true));
                }
                clause = fac.clause(List.of(domPat, hypPat, formPat, fac.refPattern(nLocal, null)), res);
            }
            clauses.add(clause);
        }
        if (onlySet)
            clauses.add(fac.clause(List.of(fac.refPattern(null, null), fac.refPattern(null, null), fac.refPattern(null, null)),
                    fac.app(fac.ref(ext.Empty.getRef()))));

        var domLocal = fac.local("dom");
        var hypLocal = fac.local("hyp");
        var formLocal = fac.local("form");
        ArendRef nLocal = null;
        if (!onlySet) nLocal = fac.local("n");

        var caseArgs = onlySet ? List.of(fac.caseArg(fac.ref(domLocal), null),
                fac.caseArg(fac.ref(hypLocal), null), fac.caseArg(fac.ref(formLocal), null)) :
                List.of(fac.caseArg(fac.ref(domLocal), null), fac.caseArg(fac.ref(hypLocal), null),
                        fac.caseArg(fac.ref(formLocal), null), fac.caseArg(fac.ref(nLocal), null));
        var caseExpr = fac.caseExpr(false,
                caseArgs, null, null, clauses);
        var lamArgs = onlySet ? Arrays.asList(fac.param(domLocal), fac.param(hypLocal), fac.param(formLocal)) :
                Arrays.asList(fac.param(domLocal), fac.param(hypLocal), fac.param(formLocal), fac.param(nLocal));
        return fac.lam(lamArgs, caseExpr);
    }

    @Dependency(module = "CategoryLanguage.Util", name = "IsubInc")
    private CoreFunctionDefinition IsubInc;

    private ConcreteExpression constructHypothesisLets(ConcreteExpression expr) {
        var typeType = fac.app(fac.ref(fp.Type.getRef()), fac.arg(fac.ref(fp.TP), true));

        var PPlam = constructHypothesislam(true);
        var PFlam = constructHypothesislam(false);

        var domLocal1 = fac.local("dom");
        var formulaType1 = fac.app(fac.ref(fp.Formula.getRef()), fac.arg(fac.ref(fp.P), true),
                fac.arg(fac.ref(fp.FP), true), fac.arg(fac.ref(domLocal1), true));
        var PPlamType = fac.pi(List.of(fac.param(true, List.of(domLocal1), typeType),
                        fac.param(true, List.of(fac.local("hyp")), formulaType1), fac.param(true, List.of(fac.local("form")), formulaType1)),
                fac.universe(null, fac.numLevel(0)));

        var domLocal = fac.local("dom");
        var formulaType = fac.app(fac.ref(fp.Formula.getRef()), fac.arg(fac.ref(fp.P), true),
                fac.arg(fac.ref(fp.FP), true), fac.arg(fac.ref(domLocal), true));
        var hypLocal = fac.local("hyp");
        var formLocal = fac.local("form");
        var nLocal = fac.local("n");
        var nType = fac.app(fac.app(fac.ref(fp.PP), fac.arg(fac.ref(domLocal), true)),
                fac.arg(fac.ref(hypLocal), true), fac.arg(fac.ref(formLocal), true));
        var PFcodomain = fac.app(fac.ref(IsubInc.getRef()),
                fac.arg(fac.ref(fp.TyF), true), fac.arg(fac.ref(fp.TeF), true),
                fac.arg(fac.ref(fp.FF), true),
                fac.arg(fac.ref(hypLocal), true), fac.arg(fac.ref(formLocal), true));
        var PFlamType = fac.pi(List.of(fac.param(true, List.of(domLocal), typeType),
                fac.param(true, List.of(hypLocal), formulaType), fac.param(true, List.of(formLocal), formulaType),
                fac.param(true, List.of(nLocal), nType)), PFcodomain);

        var PPclause = fac.letClause(fac.refPattern(fp.PP, null), PPlamType, PPlam);
        var PFclause = fac.letClause(fac.refPattern(fp.PF, null), PFlamType, PFlam);

        return fac.letExpr(false, false, List.of(PPclause, PFclause), expr);
    }

    @Dependency(module = "Paths", name = "transport")
    private CoreFunctionDefinition transport;
    @Dependency(module = "Paths", name = "*>")
    private CoreFunctionDefinition pathConcat;
    @Dependency(module = "Paths", name = "inv")
    private CoreFunctionDefinition inv;
    @Dependency(module = "Paths", name = "pmap")
    private CoreFunctionDefinition pmap;

    @Dependency(module = "CategoryLanguage.Util", name = "param-var")
    private CoreFunctionDefinition paramVar;

    CoreBinding x;
    CoreExpression ctx;
    CoreBinding p;
    CoreExpression pType;

    private ConcreteExpression constructProof(CoreExpression expr) {
        if (expr instanceof CoreFunCallExpression proofFunCall) {
            var fun = proofFunCall.getDefinition();
            var args = proofFunCall.getDefCallArguments();
            if (fun == transport) {
                var T = args.get(0);
                var f1 = args.get(1);
                if (f1 instanceof CoreInferenceReferenceExpression) {
                    f1 = ((CoreInferenceReferenceExpression) f1).getSubstExpression();
                }
                CoreExpression f1Ctx = null;
                if (f1 instanceof CoreLamExpression f1Lam) {
                    f1Ctx = f1Lam.getParameters().getTypeExpr();
                    f1 = f1Lam.getBody();
                }
                if (f1 instanceof CoreReferenceExpression) {
                    var type = f1.computeType();
                    if (type instanceof CorePiExpression typePi) {
                        f1Ctx = typePi.getParameters().getTypeExpr();
                    }
                }
                var a = args.get(2);
                var a1 = args.get(3);
                var eqProof = args.get(4);
                var proof = args.get(5);
                return fp.transportProof(constructFormula(pType, ctx).expr, constructType(T).expr, constructTerm(a, ctx).expr,
                        constructTerm(a1, ctx).expr, constructFormula(f1, f1Ctx).expr, constructProof(eqProof), constructProof(proof));
            } // transport
            if (fun == pathConcat) {
                var a = args.get(1);
                var b = args.get(2);
                var c = args.get(3);
                var abEqProof = args.get(4);
                var bcEqProof = args.get(5);
                return fp.concatProof(constructTerm(a, ctx).expr, constructTerm(b, ctx).expr,
                        constructTerm(c, ctx).expr, constructProof(abEqProof), constructProof(bcEqProof));
            } // equality conctenation
            if (fun == inv) {
                var a = args.get(1);
                var b = args.get(2);
                var eqProof = args.get(3);
                return fp.invProof(constructTerm(a, ctx).expr, constructTerm(b, ctx).expr, constructProof(eqProof));
            } // equality inversion
            if (fun == pmap) {
                var h = args.get(2);
                var a = args.get(3);
                var b = args.get(4);
                var eqProof = args.get(5);
                if (h.computeType() instanceof CorePiExpression) {
                    var hCtx = ((CorePiExpression) h.computeType()).getParameters().getTypeExpr();
                    var hType = ((CorePiExpression) h.computeType()).getCodomain();
                    ConcreteExpression hTerm = null;
                    if (h instanceof CoreInferenceReferenceExpression) {
                        h = ((CoreInferenceReferenceExpression) h).getSubstExpression();
                    }
                    if (h instanceof CoreReferenceExpression) {
                        int n = findTermNumber(hCtx, hType, (CoreReferenceExpression) h);
                        hTerm = fac.app(fac.ref(paramVar.getRef()), fac.arg(fac.ref(fp.TP), true), fac.arg(fac.ref(fp.P), true),
                                fac.arg(constructType(hCtx).expr, true), fac.arg(constructType(hType).expr, true), fac.arg(fac.number(n), true));
                    }
                    if (h instanceof CoreLamExpression hLam) {
                        hCtx = hLam.getParameters().getTypeExpr();
                        hTerm = constructTerm(hLam.getBody(), hCtx).expr;
                    }

                    return fp.pmapProof(constructTerm(a, ctx).expr, constructTerm(b, ctx).expr,
                            hTerm, constructProof(eqProof));
                }
            } // pmap function
            if (fun == ext.prelude.getIdp()) {
//                return fac.ref(ext.prelude.getIdp().getRef());
                var a = args.get(1);
                return fp.reflProof(constructTerm(a, ctx).expr, constructFormula(pType, ctx).expr);
            } // identity proof
        }
        if (expr instanceof CoreProjExpression) { // Proj
            var type = ((CoreProjExpression) expr).getExpression().computeType();
            var link = ((CoreSigmaExpression) type).getParameters();
            List<FieldsProvider.ExpressionAndPattern> types = new ArrayList<>();
            int n = 0;
            while (link.hasNext()) {
                types.add(constructFormula(link.getTypeExpr(), ctx, new ArrayList<>()));
                n++;
                link = link.getNext();
            }
            List<FieldsProvider.ExpressionAndPattern> typesCumulative = new ArrayList<>();
            FieldsProvider.ExpressionAndPattern cur = types.get(types.size() - 1);
            typesCumulative.add(cur);
            for (int i = types.size() - 2; i >= 0; i--) {
                typesCumulative.add(fp.conj(types.get(i), cur));
                cur = fp.conj(types.get(i), cur);
            }

            var term = constructProof(((CoreProjExpression) expr).getExpression());

            int ind = ((CoreProjExpression) expr).getField();
            boolean last = n == ind + 1;
            int Sind = 0;
            while (ind > 0) {
                term = fp.transProof(term, fp.proj2Proof(typesCumulative.get(typesCumulative.size() - 1 - (Sind + 1)).expr, types.get(Sind).expr));
                ind--;
                Sind++;
            }
            return last ? term : fp.transProof(term, fp.proj1Proof(types.get(Sind).expr, typesCumulative.get(typesCumulative.size() - 1 - (Sind + 1)).expr));
        } // projection in conjunction proof
        if (expr instanceof CoreTupleExpression) { // unit or Tuple
            var fields = ((CoreTupleExpression) expr).getFields();
            if (fields.size() == 0) {
                return fp.trueProof(constructType(ctx).expr, constructFormula(pType, ctx, new ArrayList<>()).expr);
            }
            var resProof = constructProof(fields.get(fields.size() - 1));
            var resFormula = constructFormula(fields.get(fields.size() - 1).computeType(), ctx, new ArrayList<>());
            for (int i = fields.size() - 2; i >= 0; i--) {
                var curProof = constructProof(fields.get(i));
                var curFormula = constructFormula(fields.get(i).computeType(), ctx, new ArrayList<>());

                resProof = fp.tupleProof(curFormula.expr, resFormula.expr, curProof, resProof);
                resFormula = fp.conj(curFormula, resFormula);
            }
            return resProof;
        } // proof of conjunction
        if (expr instanceof CoreAppExpression
                || expr instanceof CoreReferenceExpression && findHypothesis((CoreReferenceExpression) expr) != null) {

            CoreExpression fun = expr;
            ConcreteExpression term = null;
            ConcreteExpression hypProof = null;
            if (expr instanceof CoreAppExpression exprApp) {
                fun = exprApp.getFunction();

                if (fun instanceof CoreAppExpression funApp) { // hypothesis param with dom and hyp
                    fun = funApp.getFunction();
                    term = constructTerm(funApp.getArgument(), ctx, new ArrayList<>()).expr;
                    hypProof = constructProof(exprApp.getArgument());
                } else {
                    if (isType(exprApp.getArgument().computeType())) { // hypothesis param with dom only
                        term = constructTerm(exprApp.getArgument(), ctx, new ArrayList<>()).expr;
                    } else { // hypothesis with hyp only
                        hypProof = constructProof(exprApp.getArgument());
                    }
                }
            }
            if (fun instanceof CoreReferenceExpression) {
                var x = findHypothesis((CoreReferenceExpression) fun);
                var dom = x.proj1.proj1;
                var hyp = x.proj1.proj2.proj1;
                var form = x.proj1.proj2.proj2;
                if (term == null) {
                    term = fp.unit(constructType(ctx), new ArrayList<>()).expr;
                }
                if (hypProof == null) {
                    hypProof = fp.trueProof(constructType(ctx).expr, constructFormula(pType, ctx, new ArrayList<>()).expr);
                }
//                if (hypProof instanceof ConcreteReferenceExpression && ((ConcreteReferenceExpression) hypProof).getReferent() == ext.prelude.getIdp().getRef()) {
//                    if (hyp instanceof CoreFunCallExpression && ((CoreFunCallExpression) hyp).getDefinition() == ext.prelude.getEquality()) {
//                        var eq = Utils.toEquality(hyp, typechecker.getErrorReporter(), marker);
//                        var a = eq.getDefCallArguments().get(1);
//                        var b = eq.getDefCallArguments().get(2);
//                        var aTerm = constructTerm(a, dom, new ArrayList<>()).expr;
//                        var bTerm = constructTerm(b, dom, new ArrayList<>()).expr;
//                        var eqIdp = fac.app(fac.ref(ext.prelude.getIdp().getRef()));
//                        hypProof = fp.reflProof(fp.subst(aTerm, term), fp.subst(bTerm, term), constructFormula(pType, ctx, new ArrayList<>()).expr, 10, eqIdp);
//                    }
//                }
                return fp.transProof(hypProof, fp.substProof(term,
                        fp.hypothesis(constructType(dom).expr,
                                constructFormula(hyp, dom, new ArrayList<>()).expr,
                                constructFormula(form, dom, new ArrayList<>()).expr,
                                x.proj2.getIndex(fun))));
            }
        } // applying hypothesis
        if (expr instanceof CoreReferenceExpression exprRef) {
            if (exprRef.getBinding() == p) { // hyp
                return fp.idProof(constructType(ctx).expr, constructFormula(pType, ctx, new ArrayList<>()).expr);
            }
        }
        return null;

    }

    private ConcreteExpression constructFullProof(CoreExpression expr) {
        if (expr instanceof CoreLamExpression exprLam) {
            if (exprLam.getBody() instanceof CoreLamExpression exprLamLam) {
                x = exprLam.getParameters().getBinding(); // variable of dom type
                ctx = x.getTypeExpr();
                p = exprLamLam.getParameters().getBinding(); // variable of hyp type
                pType = p.getTypeExpr();
                return constructProof(exprLamLam.getBody());
            } else {
                if (isType(exprLam.getParameters().getBinding().getTypeExpr())) {
                    x = exprLam.getParameters().getBinding(); // variable of dom type, hyp = FTrue
                    ctx = x.getTypeExpr();
                    p = null;
                    pType = wrapType(ctx);
                } else {
                    p = exprLam.getParameters().getBinding(); // variable of hyp type, dom = Unit
                    pType = p.getTypeExpr();
                    ctx = sigma.getResultType();
                    x = null;
                }
                return constructProof(exprLam.getBody());
            }
        } else { // dom = Unit, hyp = FTrue
            ctx = sigma.getResultType();
            x = null;
            p = null;
            pType = wrapType(ctx);
            return constructProof(expr);
        }
    }

    @Dependency(module = "Category.Limit", name = "FinCompletePrecat")
    private CoreClassDefinition finCompletePrecat;
    @Dependency(module = "CategoryLanguage.Util", name = "subobj")
    private CoreFunctionDefinition subobj;
    @Dependency(module = "CategoryLanguage.Util", name = "subobj-inclusion")
    private CoreFunctionDefinition subobjInclusion;

    private ConcreteExpression constructLambda(ConcreteExpression proof) {
        List<ConcreteParameter> typeParams = new ArrayList<>();
        var categoryParam = fac.param(List.of(fp.category), fac.app(fac.ref(finCompletePrecat.getRef()), List.of()));
        typeParams.add(categoryParam);
        for (var x : typesParameters.getValues()) {
            typeParams.add(fac.param(List.of(getRef(x)), fac.ref(fp.category)));
        }


        List<ConcreteParameter> termPredParams = new ArrayList<>();
        for (var x : termsParameters) {
            var domType = x.proj1.proj1;
            var codType = x.proj1.proj2;
            for (var refOld : x.proj2.getValues()) {
                var homType = fac.app(fac.ref(Ih.getRef()), List.of(fac.arg(fac.ref(fp.TyF), true),
                        fac.arg(constructType(domType).expr, true), fac.arg(constructType(codType).expr, true)));
                termPredParams.add(fac.param(List.of(getRef(refOld)), homType));
            }
        }
        for (var x : predicateParameters) {
            var domType = x.proj1;
            for (var refOld : x.proj2.getValues()) {
                var domObj = fp.applyIT(constructType(domType).expr);
                var subobjType = fac.app(fac.ref(subobj.getRef()), List.of(fac.arg(domObj, true)));
                termPredParams.add(fac.param(List.of(getRef(refOld)), subobjType));
            }
        }

        List<ConcreteParameter> hypothesisParams = new ArrayList<>();
        for (var x : hypothesisParameters) {
            var dom = x.proj1.proj1;
            var hyp = x.proj1.proj2.proj1;
            var form = x.proj1.proj2.proj2;
            for (var refOld : x.proj2.getValues()) {
                var hypSubobj = fp.applyIF(constructFormula(hyp, dom, new ArrayList<>()).expr);
                var formSubobj = fp.applyIF(constructFormula(form, dom, new ArrayList<>()).expr);
                var subInclType = fac.app(fac.ref(subobjInclusion.getRef()), List.of(fac.arg(hypSubobj, true), fac.arg(formSubobj, true)));
                hypothesisParams.add(fac.param(List.of(getRef(refOld)), subInclType));
            }
        }
        return fac.lam(typeParams,
                constructTypeLets(fac.lam(termPredParams,
                        constructTermPredLets(fac.lam(hypothesisParams,
                                constructHypothesisLets(
                                        proof))))));
    }


    @Dependency(module = "CategoryLanguage.Util", name = "subst-unit")
    private static CoreFunctionDefinition substUnit;
    @Dependency(module = "CategoryLanguage.Util", name = "carry-function")
    private static CoreFunctionDefinition carryFunction;


    public ConcreteExpression handleType(ArendRef ref, CoreParameter parameter, List<ConcreteParameter> paramsAcc, ConcreteExpression application) {

        ConcreteExpression argRes = fac.ref(ref);
        ConcreteParameter paramRes = fac.param(true, List.of(ref), fac.core(parameter.getTypeExpr().computeTyped()));

        paramsAcc.add(paramRes);
        return fac.app(application, fac.arg(argRes, true));
    }

    public ConcreteExpression handleTerm(CoreParameter parameter, List<ConcreteParameter> paramsAcc, ConcreteExpression application) {
        var ref = fac.local(parameter.getBinding().getName());
        ConcreteExpression argRes;
        ConcreteParameter paramRes;

        var type = parameter.getTypeExpr();
        if (type instanceof CorePiExpression typePi) { // functional symbol
            var codomain = typePi.getCodomain();
            if (codomain instanceof CorePiExpression codPi) { // with >= two parameters
                var codomain1 = codPi.getCodomain();
                if (codomain1 instanceof CorePiExpression) { // >= 3 parameters
                    return null;
                }
                var A = fac.param(true, fac.core(typePi.getParameters().getTypedType()));
                var B = fac.param(true, fac.core(codPi.getParameters().getTypedType()));
                paramRes = fac.param(true, List.of(ref),
                        fac.pi(List.of(fac.param(true, fac.sigma(A, B))), fac.core(codomain1.computeTyped())));
                argRes = fac.app(fac.ref(carryFunction.getRef()), fac.arg(fac.ref(ref), true));
            } else { // with one parameter
                paramRes = fac.param(true, List.of(ref), fac.core(type.computeTyped()));
                argRes = fac.ref(ref);
            }
        } else { // constant symbol
            paramRes = fac.param(true, List.of(ref), fac.pi(List.of(fac.param(true, fac.sigma())), fac.core(type.computeTyped())));
            argRes = fac.app(fac.ref(substUnit.getRef()), fac.arg(fac.ref(ref), true));
        }
        paramsAcc.add(paramRes);
        return fac.app(application, fac.arg(argRes, true));
    }


    @Dependency(module = "CategoryLanguage.Util", name = "idfunc")
    private static CoreFunctionDefinition idfunc;

    public ConcreteExpression handleTerms(ConcreteExpression lam, CoreExpression lamCore, int proofStart) {



        List<ArendRef> old = new ArrayList<>();
        if (lam instanceof ConcreteLamExpression) {
            for (var p : ((ConcreteLamExpression) lam).getParameters()) {
                old.addAll(p.getRefList());
            }
        }

        var lll = typechecker.typecheck(fac.app(fac.ref(idfunc.getRef()), fac.arg(lam, true)), null).getExpression().normalize(NormalizationMode.NF);

        ConcreteExpression application = fac.core(lll.computeTyped());
        List<ConcreteParameter> parameters = new ArrayList<>();

        while (proofStart > 0) {
            if (lamCore instanceof CoreLamExpression) {
                var params = ((CoreLamExpression) lamCore).getParameters();
                while (params.hasNext()) {
                    proofStart--;
                    var type = params.getTypeExpr();
                    if (type instanceof CoreUniverseExpression) { // type parameter
                        application = handleType(old.get(0), params, parameters, application);
                    } else {
                        application = handleTerm(params, parameters, application);
                    }
                    params = params.getNext();
                }
                lamCore = ((CoreLamExpression) lamCore).getBody();
            }
        }
        return fac.lam(parameters, application);
    }



    @Override
    public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        try {
            fac = ext.factory.withData(contextData.getMarker());
            fp.init(fac, ext);
            this.typechecker = typechecker;
            marker = contextData.getMarker();
            refs = new ArrayList<>();
            typesParameters = new Values<>(typechecker, marker);
            termsParameters = new ArrayList<>();
            predicateParameters = new ArrayList<>();
            hypothesisParameters = new ArrayList<>();


            List<? extends ConcreteArgument> args = contextData.getArguments();

            var lam = args.get(0).getExpression();
            var lamCore = typechecker.typecheck(args.get(0).getExpression(), null);
            var teratsgf = fac.core(lamCore);

            var xxx = handleTerms(lam, lamCore.getExpression(), 5);
            var yyy = typechecker.typecheck(xxx, null);
            var zzz = yyy.getExpression().normalize(NormalizationMode.NF);

            int proofStart = 0;
            if (lam instanceof ConcreteLamExpression) {
                for (var p : ((ConcreteLamExpression) lam).getParameters()) {
                    proofStart += p.getRefList().size();
                }
            }
            SubstConcreteVisitor visitor = new SubstConcreteVisitor(null);
            visitor.bind();
            ((Concrete.Expression) lam).accept(visitor, null);
//            var lamCore = typechecker.typecheck(args.get(0).getExpression(), null);
            var proof = parseArgs(lamCore.getExpression(), proofStart);
            var proofConstructed = constructFullProof(proof);
            var finalProof = fp.applyIP(proofConstructed);
            var result = constructLambda(finalProof);
            var res = typechecker.typecheck(result, null);
            return res;
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }
}
