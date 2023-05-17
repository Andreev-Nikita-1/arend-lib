package org.arend.lib.meta.category_language;

import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.*;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.BaseMetaDefinition;
import org.arend.ext.typechecking.ContextData;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

public class CategoryLangMeta1 extends BaseMetaDefinition {
    private ConcreteFactory fac;
    ExpressionTypechecker typechecker;
    ErrorReporter errorReporter;
    ConcreteSourceNode marker;
    private final StdExtension ext;

    public HeytingFieldsProvider heytingFieldsProvider = new HeytingFieldsProvider();
    public RegularFieldsProvider regularFieldsProvider = new RegularFieldsProvider();
    public CoherentFieldsProvider coherentFieldsProvider = new CoherentFieldsProvider();

    public FieldsProvider fp;


    @Dependency(module = "Paths", name = "transport")
    private CoreFunctionDefinition transport;
    @Dependency(module = "Paths", name = "*>")
    private CoreFunctionDefinition pathConcat;
    @Dependency(module = "Paths", name = "inv")
    private CoreFunctionDefinition inv;
    @Dependency(module = "Paths", name = "pmap")
    private CoreFunctionDefinition pmap;
    @Dependency(module = "CategoryLanguage.Util", name = "subobj")
    private CoreFunctionDefinition subobj;
    @Dependency(module = "CategoryLanguage.Util", name = "subobj-inclusion")
    private CoreFunctionDefinition subobjInclusion;
    @Dependency(module = "CategoryLanguage.Util", name = "disjunction")
    private CoreFunctionDefinition disjunction;
    @Dependency(module = "Logic")
    private CoreDataDefinition TruncP;
    @Dependency(module = "Logic", name = "TruncP.inP")
    private CoreConstructor inP;
    @Dependency(module = "Logic", name = "Empty")
    private CoreDataDefinition Empty;
    @Dependency(module = "CategoryLanguage.Util", name = "True")
    private CoreDataDefinition True;
    @Dependency(module = "CategoryLanguage.Util", name = "True.cons")
    private CoreConstructor cons;
    @Dependency(module = "CategoryLanguage.Util", name = "recExists")
    private CoreFunctionDefinition recExists;
    @Dependency(module = "CategoryLanguage.Util", name = "recDisjunction")
    private CoreFunctionDefinition recDisjunction;
    @Dependency(module = "CategoryLanguage.Util", name = "recEmpty")
    private CoreFunctionDefinition recEmpty;
    @Dependency(module = "CategoryLanguage.Util", name = "Either.inl")
    private CoreConstructor inl;
    @Dependency(module = "CategoryLanguage.Util", name = "Either.inr")
    private CoreConstructor inr;
    @Dependency(module = "CategoryLanguage.Util", name = "Ih")
    private CoreFunctionDefinition Ih;
    @Dependency(module = "CategoryLanguage.Util", name = "Isub")
    private CoreFunctionDefinition Isub;
    @Dependency(module = "CategoryLanguage.Util", name = "type-is-set")
    private CoreFunctionDefinition TypeIsSet;
    @Dependency(module = "CategoryLanguage.Util", name = "rewriteFunc")
    private CoreFunctionDefinition RewriteFunc;
    @Dependency(module = "CategoryLanguage.Util", name = "subobj-inclusion")
    private CoreFunctionDefinition subInc;


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
                .map(x -> x.proj2).toList();
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
                .map(x -> x.proj2).toList();
        if (v.size() > 0) {
            return v.get(0).getIndex(param);
        }
        return -1;
    }

    private List<Pair<CoreExpression, Values<CoreReferenceExpression>>> predicateParameters;

    private void addPredicateParam(CoreExpression dom, CoreReferenceExpression param) {
        var v = predicateParameters.stream()
                .filter(x -> compare(x.proj1, dom))
                .map(x -> x.proj2).toList();
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
                .map(x -> x.proj2).toList();
        if (v.size() > 0) {
            return v.get(0).getIndex(param);
        }
        return -1;
    }

    private static class ProofParamData {
        CoreBinding binding;
        CoreExpression domainCore;
        CoreExpression hypCore;
        CoreExpression formCore;
        Values<CoreReferenceExpression> values;
        FieldsProvider.ExpressionAndPattern hypConstructed;
        FieldsProvider.ExpressionAndPattern formConstructed;
        ArrayList<ArendRef> pathRefs;

        public ProofParamData(CoreBinding binding, CoreExpression domainCore, CoreExpression hypCore, CoreExpression formCore, Values<CoreReferenceExpression> values) {
            this.binding = binding;
            this.domainCore = domainCore;
            this.hypCore = hypCore;
            this.formCore = formCore;
            this.values = values;
        }
    }

    private List<ProofParamData> proofParameters;

    private void addProofParam(CoreBinding binding, CoreExpression dom, CoreExpression hyp, CoreExpression form, CoreReferenceExpression param) {
        var v = proofParameters.stream()
                .filter(x -> compare(x.domainCore, dom) && compare(x.hypCore, hyp)
                        && compare(x.formCore, form))
                .map(x -> x.values).toList();
        if (v.size() == 0) {
            var values = new Values<CoreReferenceExpression>(typechecker, marker);
            values.addValue(param);
            var paramData = new ProofParamData(binding, dom, hyp, form, values);
            ctxVars.add(0, binding);
            ctxTypes.add(0, dom);
            ArrayList<ArendRef> pathRefs = new ArrayList<>();
            paramData.hypConstructed = constructFormula(hyp, pathRefs);
            paramData.formConstructed = constructFormula(form, pathRefs);
            paramData.pathRefs = pathRefs;
            ctxVars.remove(0);
            ctxTypes.remove(0);
            proofParameters.add(paramData);
        } else {
            v.get(0).addValue(param);
        }
        refs.add(new Pair<>(param, fac.local(param.getBinding().getName())));
    }

    private ProofParamData findProofParam(CoreReferenceExpression param) {
        for (var x : proofParameters) {
            if (x.values.getIndex(param) != -1) {
                return x;
            }
        }
        return null;
    }


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
            return bindings.stream().allMatch(x -> isType(x.getTypeExpr()));
        }
        if (expr instanceof CoreReferenceExpression) { // TParam
            return (typesParameters.getIndex(expr) != -1);
        }
        return false;
    }

    private void parse(CoreParameter parameter) {
        var type = parameter.getTypeExpr();
        var ref = parameter.getBinding().makeReference();
        if (type instanceof CoreUniverseExpression) { // type parameter
            addTypeParam(ref);
        } else if (type instanceof CorePiExpression typePi) {
            var codomain = typePi.getCodomain();
            if (codomain instanceof CoreUniverseExpression) { // predicate parameter
                var domain = typePi.getParameters().getTypeExpr();
                addPredicateParam(domain, ref);
            } else if (isType(codomain)) { // functional symbol
                addTermParam(typePi.getParameters().getTypeExpr(), codomain, ref);
            } else if (codomain instanceof CorePiExpression codomainPi) { // proof parameter
                var binding = typePi.getParameters().getBinding();
                var domain = typePi.getParameters().getTypeExpr();
                var hyp = codomainPi.getParameters().getTypeExpr();
                var form = codomainPi.getCodomain();
                addProofParam(binding, domain, hyp, form, ref);
            }
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


    List<CoreBinding> ctxVars = new ArrayList<>();
    List<CoreExpression> ctxTypes = new ArrayList<>();
    List<CoreBinding> ctxProofs = new ArrayList<>();
    List<CoreExpression> ctxHyps = new ArrayList<>();


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

        var TyFterm = listMap(typesParameters.getValues().stream().map(x -> fac.ref(Objects.requireNonNull(getRef(x))))
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

    private FieldsProvider.ExpressionAndPattern constructTerm(CoreExpression expr) {
        return constructTerm(expr, new ArrayList<>());
    }

    private List<FieldsProvider.ExpressionAndPattern> ctxTypesCumulative() {
        List<FieldsProvider.ExpressionAndPattern> types = new ArrayList<>();
        ctxTypes.forEach(x -> types.add(constructType(x)));
        List<FieldsProvider.ExpressionAndPattern> typesCumulative = new ArrayList<>();
        FieldsProvider.ExpressionAndPattern cur = types.get(types.size() - 1);
        typesCumulative.add(0, cur);
        for (int i = types.size() - 2; i >= 0; i--) {
            typesCumulative.add(0, fp.prodT(types.get(i), cur));
            cur = fp.prodT(types.get(i), cur);
        }
        return typesCumulative;
    }

    private FieldsProvider.ExpressionAndPattern projTerm(CoreBinding v, List<ArendRef> pathsRefs) {
        List<FieldsProvider.ExpressionAndPattern> types = new ArrayList<>();
        ctxTypes.forEach(x -> types.add(constructType(x)));
        List<FieldsProvider.ExpressionAndPattern> typesCumulative = ctxTypesCumulative();
        var term = fp.var(typesCumulative.get(0), pathsRefs);
        int ind = ctxVars.indexOf(v);
        boolean last = ctxVars.size() == ind + 1;
        int Sind = 0;
        while (ind > 0) {
            term = fp.proj2(types.get(Sind++), term, pathsRefs);
            ind--;
        }
        return last ? term : fp.proj1(typesCumulative.get(Sind + 1), term, pathsRefs);
    }

    private List<FieldsProvider.ExpressionAndPattern> ctxHypsCumulative() {
        List<FieldsProvider.ExpressionAndPattern> types = new ArrayList<>();
        ctxHyps.forEach(x -> types.add(constructFormula(x)));
        List<FieldsProvider.ExpressionAndPattern> typesCumulative = new ArrayList<>();
        FieldsProvider.ExpressionAndPattern cur = types.get(types.size() - 1);
        typesCumulative.add(0, cur);
        for (int i = types.size() - 2; i >= 0; i--) {
            typesCumulative.add(0, fp.conj(types.get(i), cur));
            cur = fp.conj(types.get(i), cur);
        }
        return typesCumulative;
    }

    private ConcreteExpression projProof(CoreBinding v) {
        List<FieldsProvider.ExpressionAndPattern> types = new ArrayList<>();
        ctxHyps.forEach(x -> types.add(constructFormula(x)));
        List<FieldsProvider.ExpressionAndPattern> typesCumulative = ctxHypsCumulative();

        var term = fp.idProof(ctxTypesCumulative().get(0).expr, typesCumulative.get(0).expr);

        int ind = ctxProofs.indexOf(v);
        boolean last = ctxProofs.size() == ind + 1;
        int Sind = 0;
        while (ind > 0) {
            term = fp.transProof(term, fp.proj2Proof(typesCumulative.get(Sind + 1).expr, types.get(Sind).expr));
            ind--;
            Sind++;
        }
        return last ? term : fp.transProof(term, fp.proj1Proof(types.get(Sind).expr, typesCumulative.get(Sind + 1).expr));
    }

    private FieldsProvider.ExpressionAndPattern constructTerm(CoreExpression expr, List<ArendRef> pathsRefs) {
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
                    return fp.param(constructTerm(arg, pathsRefs), constructType(cod), constructType(dom),
                            findTermNumber(dom, cod, funRef), pathsRefs);
            }
        }
        if (expr instanceof CoreReferenceExpression exprRef) { // Var
            var ref = exprRef.getBinding();
            return projTerm(ref, pathsRefs);
        }
        if (expr instanceof CoreTupleExpression) { // unit or Tuple
            var fields = ((CoreTupleExpression) expr).getFields();
            if (fields.size() == 0) {
                return fp.unit(ctxTypesCumulative().get(0), pathsRefs);
            }
            var res = constructTerm(fields.get(fields.size() - 1), pathsRefs);
            var resType = constructType(fields.get(fields.size() - 1).computeType());
            for (int i = fields.size() - 2; i >= 0; i--) {
                var cur = constructTerm(fields.get(i), pathsRefs);
                var curType = constructType(fields.get(i).computeType());

                res = fp.tuple(cur, res, curType, resType, pathsRefs);
                resType = fp.prodT(curType, resType);
            }
            return res;
        }
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
            var term = constructTerm(((CoreProjExpression) expr).getExpression(), pathsRefs);
            int ind = ((CoreProjExpression) expr).getField();
            boolean last = n == ind + 1;
            int Sind = 0;
            while (ind > 0) {
                term = fp.proj2(types.get(Sind++), term, pathsRefs);
                ind--;
            }
            return last ? term : fp.proj1(typesCumulative.get(typesCumulative.size() - 1 - (Sind + 1)), term, pathsRefs);
        }
        return null;
    }

    private FieldsProvider.ExpressionAndPattern constructFormula(CoreExpression expr) {
        return constructFormula(expr, new ArrayList<>());
    }

    private FieldsProvider.ExpressionAndPattern constructFormula(CoreExpression expr, List<ArendRef> pathsRefs) {
        if (expr instanceof CoreSigmaExpression) { // conjunction
            var link = ((CoreSigmaExpression) expr).getParameters();
            try {
                link.getBinding().getName();
            } catch (IllegalStateException e) {
                fp.ftrue(ctxTypesCumulative().get(0));
            }
            List<CoreBinding> bindings = new ArrayList<>();
            while (link.hasNext()) {
                bindings.add(link.getBinding());
                link = link.getNext();
            }
            var res = constructFormula(bindings.get(bindings.size() - 1).getTypeExpr(), pathsRefs);
            for (int i = bindings.size() - 2; i >= 0; i--) {
                var cur = constructFormula(bindings.get(i).getTypeExpr(), pathsRefs);
                res = fp.conj(cur, res);
            }
            return res;
        }
        if (expr instanceof CoreDataCallExpression dataCall) {
            if (dataCall.getDefinition() == ext.prelude.getPath()) { //equality
                var eq = Utils.toEquality(expr, typechecker.getErrorReporter(), marker);
                var a = eq.getDefCallArguments().get(1);
                var b = eq.getDefCallArguments().get(2);
                var T = a.computeType();
                return fp.Eq(constructTerm(a, pathsRefs), constructTerm(b, pathsRefs), constructType(T));
            }
        }

        if (expr instanceof CoreFunCallExpression funCall) {
            if (funCall.getDefinition() == ext.prelude.getEquality()) { //equality
                var eq = Utils.toEquality(expr, typechecker.getErrorReporter(), marker);
                var a = eq.getDefCallArguments().get(1);
                var b = eq.getDefCallArguments().get(2);
                var T = a.computeType();
                return fp.Eq(constructTerm(a, pathsRefs), constructTerm(b, pathsRefs), constructType(T));
            }

            if (funCall.getDefinition() == disjunction) { // Disj
                var args = funCall.getDefCallArguments();
                var a = args.get(0);
                var b = args.get(1);
                return fp.disj(constructFormula(a, pathsRefs), constructFormula(b, pathsRefs));
            }
        }

        if (expr instanceof CoreAppExpression appExpr) {
            var fun = appExpr.getFunction();
            var arg = appExpr.getArgument();
            var type = fun.computeType();
            if (type instanceof CorePiExpression piType) {
                if (fun instanceof CoreReferenceExpression funRef) {
                    var dom1 = piType.getParameters().getTypeExpr();
                    return fp.fparam(findPredicateNumber(dom1, funRef), constructTerm(arg, pathsRefs), constructType(dom1));
                }
            }
        }

        if (expr instanceof CorePiExpression piExpr) {
            var paramType = piExpr.getParameters().getTypeExpr();
            if (isType(paramType)) { // Forall
                var var = piExpr.getParameters().getBinding();
                ctxVars.add(0, var);
                ctxTypes.add(0, paramType);
                var res = constructFormula(piExpr.getCodomain(), pathsRefs);
                ctxVars.remove(0);
                ctxTypes.remove(0);
                return fp.forall(constructType(paramType), res);
            } else { // Impl
                var var = piExpr.getParameters().getBinding();
                var res = constructFormula(piExpr.getCodomain(), pathsRefs);
                return fp.impl(constructFormula(paramType, pathsRefs), res);
            }
        }

        if (expr instanceof CoreDataCallExpression dataCall) {


            if (dataCall.getDefinition() == ext.TruncP) { // Exists
                var args = dataCall.getDefCallArguments().get(0);
                if (args instanceof CoreSigmaExpression sigmaExpr) {
                    var var = sigmaExpr.getParameters().getBinding();
                    var paramType = sigmaExpr.getParameters().getTypeExpr();
                    var form = sigmaExpr.getParameters().getNext().getTypeExpr();
                    ctxVars.add(0, var);
                    ctxTypes.add(0, paramType);
                    var res = constructFormula(form, pathsRefs);
                    ctxVars.remove(0);
                    ctxTypes.remove(0);
                    return fp.exists(constructType(paramType), res);
                }
            }

            if (dataCall.getDefinition() == True) {
                return fp.ftrue(ctxTypesCumulative().get(0));
            }
            if (dataCall.getDefinition() == Empty) {
                return fp.ffalse(ctxTypesCumulative().get(0));
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
                        .map(x -> fac.ref(Objects.requireNonNull(getRef(x)))).collect(Collectors.toList());
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
                        .map(x -> fac.ref(Objects.requireNonNull(getRef(x)))).collect(Collectors.toList());
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


    private ConcreteExpression constructTermPredLets(ConcreteExpression expr) {

        var typeType = fac.app(fac.ref(fp.getType().getRef()), fac.arg(fac.ref(fp.TP), true));

        var Plam = constructTermlam(true);
        var TeFlam = constructTermlam(false);

        var PlamType = fac.pi(List.of(fac.param(true, List.of(fac.local("dom")), typeType),
                fac.param(true, List.of(fac.local("cod")), typeType)), fac.universe(null, fac.numLevel(0)));

        var domLocal = fac.local("dom");
        var codLocal = fac.local("cod");
        var nLocal = fac.local("n");
        var nType = fac.app(fac.app(fac.ref(fp.P), fac.arg(fac.ref(domLocal), true)),
                fac.arg(fac.ref(codLocal), true));
        var TeFcodomain = fac.app(fac.app(fac.app(fac.core(((CoreLamExpression) Ih.getActualBody()).computeTyped()),
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

    private ConcreteExpression constructProofslam(boolean onlySet) {
        List<ConcreteClause> clauses = new ArrayList<>();
        var all = proofParameters;
        for (var p : all) {
            var domPat = constructType(p.domainCore).pattern;
            ConcreteClause clause;
            if (onlySet) {
                clause = fac.clause(List.of(domPat, p.hypConstructed.pattern, p.formConstructed.pattern),
                        fac.app(fac.ref(ext.prelude.getFin().getRef()),
                                fac.arg(fac.number(p.values.getValues().size()), true)));
            } else {
                var nLocal = fac.local("n");
                var args = p.values.getValues().stream()
                        .map(x -> fac.ref(Objects.requireNonNull(getRef(x)))).collect(Collectors.toList());
                var res = fac.app(listMap(args), fac.arg(fac.ref(nLocal), true));
                for (var path : p.pathRefs) {
                    var idpEq = fac.app(fac.ref(TypeIsSet.getRef()), fac.arg(fac.ref(path), true));
                    res = fac.app(fac.ref(RewriteFunc.getRef()), fac.arg(idpEq, true), fac.arg(res, true));
                }
                clause = fac.clause(List.of(domPat, p.hypConstructed.pattern, p.formConstructed.pattern, fac.refPattern(nLocal, null)), res);
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


    private ConcreteExpression constructProofsLets(ConcreteExpression expr) {
        var typeType = fac.app(fac.ref(fp.getType().getRef()), fac.arg(fac.ref(fp.TP), true));

        var PPlam = constructProofslam(true);
        var PFlam = constructProofslam(false);

        var domLocal1 = fac.local("dom");
        var formulaType1 = fac.app(fac.ref(fp.getFormula().getRef()), fac.arg(fac.ref(fp.P), true),
                fac.arg(fac.ref(fp.FP), true), fac.arg(fac.ref(domLocal1), true));
        var PPlamType = fac.pi(List.of(fac.param(true, List.of(domLocal1), typeType),
                        fac.param(true, List.of(fac.local("hyp")), formulaType1), fac.param(true, List.of(fac.local("form")), formulaType1)),
                fac.universe(null, fac.numLevel(0)));

        var domLocal = fac.local("dom");
        var formulaType = fac.app(fac.ref(fp.getFormula().getRef()), fac.arg(fac.ref(fp.P), true),
                fac.arg(fac.ref(fp.FP), true), fac.arg(fac.ref(domLocal), true));
        var hypLocal = fac.local("hyp");
        var formLocal = fac.local("form");
        var nLocal = fac.local("n");
        var nType = fac.app(fac.app(fac.ref(fp.PP), fac.arg(fac.ref(domLocal), true)),
                fac.arg(fac.ref(hypLocal), true), fac.arg(fac.ref(formLocal), true));
        var PFcodomain = fac.app(fac.ref(subInc.getRef()), fac.arg(fp.applyIF(fac.ref(hypLocal)), true), fac.arg(fp.applyIF(fac.ref(formLocal)), true));
        var PFlamType = fac.pi(List.of(fac.param(true, List.of(domLocal), typeType),
                fac.param(true, List.of(hypLocal), formulaType), fac.param(true, List.of(formLocal), formulaType),
                fac.param(true, List.of(nLocal), nType)), PFcodomain);

        var PPclause = fac.letClause(fac.refPattern(fp.PP, null), PPlamType, PPlam);
        var PFclause = fac.letClause(fac.refPattern(fp.PF, null), PFlamType, PFlam);

        return fac.letExpr(false, false, List.of(PPclause, PFclause), expr);
    }


    private ConcreteExpression constructFullProof(CoreExpression expr) {
        if (expr instanceof CoreLamExpression exprLam) {
            var paramType = exprLam.getParameters().getTypeExpr();
            var var = exprLam.getParameters().getBinding();
            if (exprLam.getBody() instanceof CoreLamExpression exprLamLam) {
                ctxVars.add(0, var);
                ctxTypes.add(0, paramType);
                var paramType1 = exprLamLam.getParameters().getTypeExpr();
                var var1 = exprLamLam.getParameters().getBinding();
                ctxProofs.add(0, var1);
                ctxHyps.add(0, paramType1);
                var hyp = ctxHypsCumulative().get(0).expr;
                var res = constructProof(exprLamLam.getBody());
                ctxHyps.remove(0);
                ctxProofs.remove(0);
                ctxTypes.remove(0);
                ctxVars.remove(0);
                return fp.applyIP(hyp, res);
            }
        }
        return null;
    }

    private ConcreteExpression constructProof(CoreExpression expr) {

        if (expr instanceof CoreLamExpression exprLam) {
            var paramType = exprLam.getParameters().getTypeExpr();
            if (isType(paramType)) { // forall abstraction
                var var = exprLam.getParameters().getBinding();
                ctxVars.add(0, var);
                ctxTypes.add(0, paramType);
                var res = constructProof(exprLam.getBody());
                ctxVars.remove(0);
                ctxTypes.remove(0);
                return fp.abstrForallProof(res);
            } else { // impl abstraction
                var var = exprLam.getParameters().getBinding();
                ctxProofs.add(0, var);
                ctxHyps.add(0, paramType);
                var res = constructProof(exprLam.getBody());
                ctxProofs.remove(0);
                ctxHyps.remove(0);
                return fp.abstrImplProof(res);
            }
        }

        if (expr instanceof CoreAppExpression exprApp) {
            var func = exprApp.getFunction();
            var arg = exprApp.getArgument();

            if (func instanceof CoreAppExpression funcApp) {
                var func1 = funcApp.getFunction();
                if (func1 instanceof CoreReferenceExpression && findProofParam((CoreReferenceExpression) func1) != null) { // applying proof parameter
                    var proofParamData = findProofParam((CoreReferenceExpression) func1);
                    assert proofParamData != null;
                    int n = proofParamData.values.getIndex((CoreReferenceExpression) func1);
                    return fp.paramProof(proofParamData.hypConstructed.expr, proofParamData.formConstructed.expr,
                            constructTerm(funcApp.getArgument()).expr, constructProof(arg), n);
                }
            }

            if (isType(arg.computeType())) { // forall application
                return fp.appForallProof(constructProof(func), constructTerm(arg).expr);
            } else { // impl application
                return fp.appImplProof(constructProof(arg), constructProof(func));
            }
        }


        if (expr instanceof CoreFunCallExpression proofFunCall) {
            var fun = proofFunCall.getDefinition();
            var args = proofFunCall.getDefCallArguments();
            if (fun == transport) {
                var T = args.get(0);
                var f1 = args.get(1);

                if (f1 instanceof CoreInferenceReferenceExpression f1Inf) {
                    f1 = f1Inf.getSubstExpression();
                }
                if (f1 instanceof CoreLamExpression f1Lam) {
                    var var = f1Lam.getParameters().getBinding();
                    var paramType = var.getTypeExpr();
                    ctxVars.add(0, var);
                    ctxTypes.add(0, paramType);
                    var form = constructFormula(f1Lam.getBody());
                    ctxVars.remove(0);
                    ctxTypes.remove(0);
                    var a = args.get(2);
                    var a1 = args.get(3);
                    var eqProof = args.get(4);
                    var proof = args.get(5);
                    return fp.transportProof(ctxHypsCumulative().get(0).expr, constructType(T).expr, constructTerm(a).expr,
                            constructTerm(a1).expr, form.expr, constructProof(eqProof), constructProof(proof));
                }
            }
            if (fun == pathConcat) {
                var a = args.get(1);
                var b = args.get(2);
                var c = args.get(3);
                var abEqProof = args.get(4);
                var bcEqProof = args.get(5);
                return fp.concatProof(constructTerm(a).expr, constructTerm(b).expr,
                        constructTerm(c).expr, constructProof(abEqProof), constructProof(bcEqProof));
            }
            if (fun == inv) {
                var a = args.get(1);
                var b = args.get(2);
                var eqProof = args.get(3);
                return fp.invProof(constructTerm(a).expr, constructTerm(b).expr, constructProof(eqProof));
            }
            if (fun == pmap) {
                var h = args.get(2);
                var a = args.get(3);
                var b = args.get(4);
                var eqProof = args.get(5);
                if (h instanceof CoreInferenceReferenceExpression hInf) {
                    h = hInf.getSubstExpression();
                }
                if (h instanceof CoreLamExpression hLam) {
                    var var = hLam.getParameters().getBinding();
                    var paramType = var.getTypeExpr();
                    ctxVars.add(0, var);
                    ctxTypes.add(0, paramType);
                    var hTerm = constructTerm(hLam.getBody()).expr;
                    ctxVars.remove(0);
                    ctxTypes.remove(0);
                    return fp.pmapProof(constructTerm(a).expr, constructTerm(b).expr,
                            hTerm, constructProof(eqProof));
                }
            }
            if (fun == ext.prelude.getIdp()) {
                var a = args.get(1);
                return fp.reflProof(constructTerm(a).expr, (ctxHypsCumulative().get(0)).expr);
            }
            if (fun == recEmpty) {
                var f = constructFormula(args.get(0)).expr;
                var p = constructProof(args.get(1));
                return fp.absurdProof(f, p);
            }
            if (fun == recDisjunction) {
                var h1 = proofFunCall.getDefCallArguments().get(3);
                var h2 = proofFunCall.getDefCallArguments().get(4);
                var disjProof = constructProof(proofFunCall.getDefCallArguments().get(5));

                ConcreteExpression proof1 = null;
                if (h1 instanceof CoreLamExpression h1lam) {
                    var hyp1 = h1lam.getParameters().getBinding();
                    ctxProofs.add(0, hyp1);
                    ctxHyps.add(0, hyp1.getTypeExpr());
                    proof1 = constructProof(h1lam.getBody());
                    ctxProofs.remove(0);
                    ctxHyps.remove(0);
                }

                ConcreteExpression proof2 = null;
                if (h2 instanceof CoreLamExpression h2lam) {
                    var hyp2 = h2lam.getParameters().getBinding();
                    ctxProofs.add(0, hyp2);
                    ctxHyps.add(0, hyp2.getTypeExpr());
                    proof2 = constructProof(h2lam.getBody());
                    ctxProofs.remove(0);
                    ctxHyps.remove(0);
                }
                return fp.recDisjProof(disjProof, proof1, proof2);
            }
            if (fun == recExists) {
                var h = args.get(3);
                var exProof = args.get(4);

                var sigmaType = exProof.computeType();
                if (sigmaType instanceof CoreDataCallExpression dataCallExpression) {
                    sigmaType = dataCallExpression.getDefCallArguments().get(0);
                }
                ConcreteExpression f1 = null;
                if (sigmaType instanceof CoreSigmaExpression sigmaExpression) {
                    ctxVars.add(0, sigmaExpression.getParameters().getBinding());
                    ctxTypes.add(0, sigmaExpression.getParameters().getTypeExpr());
                    f1 = constructFormula(sigmaExpression.getParameters().getNext().getTypeExpr()).expr;
                    ctxVars.remove(0);
                    ctxTypes.remove(0);
                }

                var f = constructFormula(expr.computeType());

                ConcreteExpression res = null;

                if (h instanceof CoreLamExpression exprLam) {
                    var paramType = exprLam.getParameters().getTypeExpr();
                    var var = exprLam.getParameters().getBinding();

                    ctxVars.add(0, var);
                    ctxTypes.add(0, paramType);
                    if (exprLam.getBody() instanceof CoreLamExpression exprLam1) {
                        var var1 = exprLam1.getParameters().getBinding();
                        var paramType1 = exprLam1.getParameters().getTypeExpr();
                        ctxProofs.add(0, var1);
                        ctxHyps.add(0, paramType1);
                        res = constructProof(exprLam1.getBody());
                        ctxProofs.remove(0);
                        ctxHyps.remove(0);
                    }
                    ctxVars.remove(0);
                    ctxTypes.remove(0);
                }


                return fp.recExistsProof(f.expr, f1, constructProof(exProof), res);
            }
        }
        if (expr instanceof CoreProjExpression) { // Proj
            var type = ((CoreProjExpression) expr).getExpression().computeType();
            var link = ((CoreSigmaExpression) type).getParameters();
            List<FieldsProvider.ExpressionAndPattern> types = new ArrayList<>();
            int n = 0;
            while (link.hasNext()) {
                types.add(constructFormula(link.getTypeExpr()));
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
        }
        if (expr instanceof CoreTupleExpression) {
            var fields = ((CoreTupleExpression) expr).getFields();
            if (fields.size() == 0) {
                return fp.trueProof(ctxTypesCumulative().get(0).expr, ctxHypsCumulative().get(0).expr);
            }
            var resProof = constructProof(fields.get(fields.size() - 1));
            var resFormula = constructFormula(fields.get(fields.size() - 1).computeType());
            for (int i = fields.size() - 2; i >= 0; i--) {
                var curProof = constructProof(fields.get(i));
                var curFormula = constructFormula(fields.get(i).computeType());

                resProof = fp.tupleProof(curFormula.expr, resFormula.expr, curProof, resProof);
                resFormula = fp.conj(curFormula, resFormula);
            }
            return resProof;
        }
        if (expr instanceof CoreReferenceExpression exprRef) {
            return projProof(exprRef.getBinding());
        }
        if (expr instanceof CoreDefCallExpression exprDefCall) {
            if (exprDefCall.getDefinition() == cons) {
                return fp.trueProof(ctxTypesCumulative().get(0).expr, ctxHypsCumulative().get(0).expr);
            }
            if (exprDefCall.getDefinition() == inP) {
                var arg0 = exprDefCall.getDefCallArguments().get(0);
                if (arg0 instanceof CoreTupleExpression argTuple) { // exists constructor
                    var term = constructTerm(argTuple.getFields().get(0));
                    var proof = constructProof(argTuple.getFields().get(1));
                    ctxVars.add(0, argTuple.getSigmaType().getParameters().getBinding());
                    ctxTypes.add(0, argTuple.getSigmaType().getParameters().getTypeExpr());
                    var xxx = argTuple.getSigmaType().getParameters().getNext().getTypeExpr();
                    var formula = constructFormula(xxx);
                    ctxVars.remove(0);
                    ctxTypes.remove(0);
                    return fp.existsConsProof(formula.expr, term.expr, proof);
                }
                if (arg0 instanceof CoreConCallExpression conCall) {
                    if (conCall.getDefinition() == inl) {
                        var f2 = constructFormula(conCall.getDataTypeArguments().get(1)).expr;
                        return fp.inlProof(f2, constructProof(conCall.getDefCallArguments().get(0)));
                    }
                    if (conCall.getDefinition() == inr) {
                        var f1 = constructFormula(conCall.getDataTypeArguments().get(0)).expr;
                        return fp.inrProof(f1, constructProof(conCall.getDefCallArguments().get(0)));
                    }
                }
            }
        }
        return null;
    }

    private ConcreteExpression constructLambda(ConcreteExpression proof) {
        List<ConcreteParameter> typeParams = new ArrayList<>();
        var categoryParam = fac.param(List.of(fp.category), fac.app(fac.ref(fp.getCategoryDef().getRef()), List.of()));
        typeParams.add(categoryParam);
        for (var x : typesParameters.getValues()) {
            typeParams.add(fac.param(List.of(Objects.requireNonNull(getRef(x))), fac.ref(fp.category)));
        }


        List<ConcreteParameter> termPredParams = new ArrayList<>();
        for (var x : termsParameters) {
            var domType = x.proj1.proj1;
            var codType = x.proj1.proj2;
            for (var refOld : x.proj2.getValues()) {
                var homType = fac.app(fac.core(((CoreLamExpression) Ih.getActualBody()).computeTyped()), List.of(fac.arg(fac.ref(fp.TyF), true),
                        fac.arg(constructType(domType).expr, true), fac.arg(constructType(codType).expr, true)));
                termPredParams.add(fac.param(List.of(Objects.requireNonNull(getRef(refOld))), homType));
            }
        }
        for (var x : predicateParameters) {
            var domType = x.proj1;
            for (var refOld : x.proj2.getValues()) {
                var domObj = fp.applyIT(constructType(domType).expr);
                var subobjType = fac.app(fac.ref(subobj.getRef()), List.of(fac.arg(domObj, true)));
                termPredParams.add(fac.param(List.of(Objects.requireNonNull(getRef(refOld))), subobjType));
            }
        }

        List<ConcreteParameter> hypothesisParams = new ArrayList<>();
        for (var x : proofParameters) {
            for (var refOld : x.values.getValues()) {
                ctxVars.add(0, x.binding);
                ctxTypes.add(0, x.domainCore);
                var hypSubobj = fp.applyIF(x.hypConstructed.expr);
                var formSubobj = fp.applyIF(x.formConstructed.expr);
                ctxVars.remove(0);
                ctxTypes.remove(0);
                var subInclType = fac.app(fac.ref(subobjInclusion.getRef()), List.of(fac.arg(hypSubobj, true), fac.arg(formSubobj, true)));
                hypothesisParams.add(fac.param(List.of(Objects.requireNonNull(getRef(refOld))), subInclType));
            }
        }
        return fac.lam(typeParams,
                constructTypeLets(fac.lam(termPredParams,
                        constructTermPredLets(fac.lam(hypothesisParams,
                                constructProofsLets(
                                        proof))))));
    }

    public Canonizer canonizer = new Canonizer();

    @Override
    public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        try {
            fac = ext.factory.withData(contextData.getMarker());
            this.typechecker = typechecker;
            errorReporter = typechecker.getErrorReporter();
            marker = contextData.getMarker();


            List<? extends ConcreteArgument> args = contextData.getArguments();
            ConcreteExpression input = null;
            if (args.size() == 1) {
                input = args.get(0).getExpression();
                fp = heytingFieldsProvider;
            } else if (args.size() == 2) {
                var arg0 = args.get(0).getExpression();
                if (arg0 instanceof ConcreteStringExpression stringExpression) {
                    var categoryType = stringExpression.getUnescapedString();
                    switch (categoryType) {
                        case "regular" -> fp = regularFieldsProvider;
                        case "coherent" -> fp = coherentFieldsProvider;
                        case "heyting" -> fp = heytingFieldsProvider;
                        default -> {
                            errorReporter.report(new TypecheckingError("In case there are two arguments, first argument has to be string literal 'regular', 'coherent' or 'heyting'", marker));
                            return null;
                        }
                    }
                    input = args.get(1).getExpression();
                } else {
                    errorReporter.report(new TypecheckingError("In case there are two arguments, first argument has to be string literal 'regular', 'coherent' or 'heyting'", marker));
                    return null;
                }
            } else {
                errorReporter.report(new TypecheckingError("Function can take one or two arguments" +
                        "In case there are two arguments, first argument has to be string literal 'regular', 'coherent' or 'heyting'" +
                        "Last argument must be lambda function, that have sets parameters, functional parameters, predicate parameters and hypothesis parameters", marker));
                return null;
            }

            fp.init(fac, ext, errorReporter, marker);

            refs = new ArrayList<>();
            typesParameters = new Values<>(typechecker, marker);
            termsParameters = new ArrayList<>();
            predicateParameters = new ArrayList<>();
            proofParameters = new ArrayList<>();

            var lam = input;
            var lamCore = typechecker.typecheck(input, null);
            if (lamCore == null || lamCore.getExpression() instanceof CoreErrorExpression) {
                errorReporter.report(new TypecheckingError("Error when typechecking input", marker));
                return null;
            }

            int proofStart = 0;
            if (lam instanceof ConcreteLamExpression) {
                for (var p : ((ConcreteLamExpression) lam).getParameters()) {
                    proofStart += p.getRefList().size();
                }
            } else {
                errorReporter.report(new TypecheckingError("Input has to be lambda expression", marker));
                return null;
            }
            canonizer.init(fac, ext, typechecker, marker);
            var canonized = canonizer.canonize(lamCore.getExpression(), proofStart);
            if (canonized == null) {
                return null;
            }

            var proof = parseArgs(canonized, proofStart);
            var proofConstructed = constructFullProof(proof);
            var result = constructLambda(proofConstructed);
            var res = typechecker.typecheck(result, null);
            return res;
        } catch (Throwable e) {
            e.printStackTrace();
        }
        return null;
    }
}
