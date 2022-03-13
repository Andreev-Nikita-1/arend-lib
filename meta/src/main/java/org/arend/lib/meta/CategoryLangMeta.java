package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.concrete.pattern.ConcretePattern;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.expr.*;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.jetbrains.annotations.NotNull;

import java.util.*;
import java.util.stream.Collectors;

public class CategoryLangMeta extends BaseMetaDefinition {
    private final StdExtension ext;


    public CategoryLangMeta(StdExtension ext) {
        this.ext = ext;
    }

    @Override
    public boolean[] argumentExplicitness() {
        return new boolean[]{true};
    }

    private static class NamesHolder {
        List<String> oldNames;
        List<String> newNames;
        List<String> obsNames = new ArrayList<>();
        Map<Pair<String, String>, List<String>> morsOldNames = new HashMap<>();
        Map<String, CoreExpression> doms = new HashMap<>();
        Map<String, CoreExpression> cods = new HashMap<>();
        TypesTranslator translator;

        public NamesHolder(TypesTranslator translator) {
            this.translator = translator;
        }

        public CoreExpression set(CoreExpression lam, CoreExpression type, List<ConcreteParameter> params) {
            List<CoreParameter> oldParams = new ArrayList<>();
            for (int i = 0; i < params.size(); i++) {
                oldParams.add(((CorePiExpression) type).getParameters());
                type = ((CorePiExpression) type).getCodomain();
            }
            oldNames = params.stream().flatMap(concreteParameter -> concreteParameter.getRefList().stream().map(ArendRef::getRefName)).collect(Collectors.toList());
            List<CoreParameter> newVars = new ArrayList<>();
            for (int i = 0; i < oldNames.size(); i++) {
                newVars.add(((CoreLamExpression) lam).getParameters());
                lam = ((CoreLamExpression) lam).getBody();
            }
            newNames = newVars.stream().map(x -> x.getBinding().getName()).collect(Collectors.toList());

            for (CoreParameter p : oldParams) {
                var type1 = p.getTypeExpr();
                List<String> oldNames1 = new ArrayList<>();
                oldNames1.add(p.getBinding().getName());
                while (p.hasNext()) {
                    p = p.getNext();
                    try {
                        oldNames1.add(p.getBinding().getName());
                    } catch (IllegalStateException ignored) {
                    }
                }
                var newNames1 = oldNames1.stream().map(x -> newNames.get(oldNames.indexOf(x))).collect(Collectors.toList());
                if (type1 instanceof CorePiExpression) {
                    var dom = ((CorePiExpression) type1).getParameters().getTypeExpr();
                    var cod = ((CorePiExpression) type1).getCodomain();
                    doms.put(dom.toString(), dom);
                    cods.put(cod.toString(), cod);
                    morsOldNames.put(new Pair<>(dom.toString(), cod.toString()), newNames1);
                }
                if (type1 instanceof CoreUniverseExpression) {
                    obsNames = newNames1;
                }
            }
            return lam;
        }

        public CoreExpression oldRef(String name) {
            return translator.oldRefs.get(name);
        }

        public String newToOld(String newName) {
            return oldNames.get(newNames.indexOf(newName));
        }
    }

    private static class TypeTermFactory {
        StdExtension ext;
        ConcreteFactory fac;
        NamesHolder nh;
        ArendRef obs;
        ArendRef obsMap;
        ArendRef mors;
        ArendRef morsMap;

        ConcreteExpression ctx;
        String var;


        public TypeTermFactory(StdExtension ext, ConcreteFactory fac, NamesHolder nh) {
            this.ext = ext;
            this.fac = fac;
            this.nh = nh;
            obs = fac.local("obs");
            obsMap = fac.local("obsMap");
            mors = fac.local("mors");
            morsMap = fac.local("morsMap");

        }

        public ConcreteExpression paramT(int i) {
            return fac.app(fac.ref(ext.TParam.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.number(i), true));
        }

        public ConcreteExpression prodT(ConcreteExpression a, ConcreteExpression b) {
            return fac.app(fac.ref(ext.Prod.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(a, true), fac.arg(b, true));
        }

        public ConcreteExpression unitT() {
            return fac.app(fac.ref(ext.Unit.getRef()),
                    fac.arg(fac.ref(obs), false));
        }

        public ConcreteExpression tuple(ConcreteExpression a, ConcreteExpression b) {
            return fac.app(fac.ref(ext.Tuple.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false),
                    fac.arg(a, true), fac.arg(b, true));
        }

        public ConcreteExpression unit() {
            return fac.app(fac.ref(ext.unit.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false));
        }

        public ConcreteExpression proj1(ConcreteExpression t) {
            return fac.app(fac.ref(ext.Proj1.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false),
                    fac.arg(t, true));
        }

        public ConcreteExpression proj2(ConcreteExpression t) {
            return fac.app(fac.ref(ext.Proj2.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false),
                    fac.arg(t, true));
        }

        public ConcreteExpression param(ConcreteExpression T, int i) {
            return fac.app(fac.ref(ext.Param.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false),
                    fac.arg(T, false), fac.arg(fac.number(i), true));
        }

        public ConcreteExpression var() {
            return fac.app(fac.ref(ext.Var.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false),
                    fac.arg(ctx, false), fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true));
        }

        public ConcreteExpression applyI(ConcreteExpression term) {
            return fac.app(fac.ref(ext.I.getRef()), fac.arg(fac.ref(obsMap), true),
                    fac.arg(fac.ref(morsMap), true), fac.arg(term, true));
        }

        private ConcreteExpression listMap(List<ConcreteExpression> args) {
            var res = fac.app(fac.ref(ext.nil.getRef()));
            for (int i = args.size() - 1; i >= 0; i--) {
                var res1 = fac.app(fac.ref(ext.cons.getRef()),
                        fac.arg(args.get(i), true));
                res = fac.app(res1, fac.arg(res, true));
            }
            return fac.app(fac.ref(ext.at.getRef()), fac.arg(res, true));
        }

        private ConcreteExpression morsLam(boolean onlySet) {
            List<ConcreteClause> clauses = new ArrayList<>();
            for (var p : nh.morsOldNames.keySet()) {
                var domExpr = nh.doms.get(p.proj1);
                var codExpr = nh.cods.get(p.proj2);
                var domPat = constructPattern(domExpr);
                var codPat = constructPattern(codExpr);
                ConcreteClause clause;
                if (onlySet) {
                    clause = fac.clause(List.of(domPat, codPat),
                            fac.app(fac.ref(ext.prelude.getFin().getRef()),
                                    fac.arg(fac.number(nh.morsOldNames.get(p).size()), true)));
                } else {
                    var nLocal = fac.local("n");
                    var morsArgs = nh.morsOldNames.get(p).stream().map(nh::newToOld)
                            .map(nm -> fac.core(nh.oldRef(nm).computeTyped())).collect(Collectors.toList());
                    clause = fac.clause(List.of(domPat, codPat, fac.refPattern(nLocal, null)),
                            fac.app(listMap(morsArgs), fac.arg(fac.ref(nLocal), true)));
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

        public ConcreteExpression addParameterMaps(ConcreteExpression expression) {
            var obsTerm = fac.app(fac.ref(ext.prelude.getFin().getRef()),
                    fac.arg(fac.number(nh.obsNames.size()), true));
            var obsArgs = nh.obsNames.stream().map(nh::newToOld)
                    .map(nm -> fac.core(nh.oldRef(nm).computeTyped())).collect(Collectors.toList());
            var obsMapTerm = listMap(obsArgs);

            var morsTerm = morsLam(true);
            var morsMapTerm = morsLam(false);

            var typeObs = fac.app(fac.ref(ext.Type.getRef()), fac.arg(fac.ref(obs), true));

            var domLocal = fac.local("dom");
            var codLocal = fac.local("cod");
            var morsType = fac.pi(List.of(fac.param(true, List.of(domLocal), typeObs),
                    fac.param(true, List.of(codLocal), typeObs)), fac.universe(null, fac.numLevel(0)));

            domLocal = fac.local("dom");
            codLocal = fac.local("cod");
            var nLocal = fac.local("n");
            var nType = fac.app(fac.app(fac.ref(mors), fac.arg(fac.ref(domLocal), true)),
                    fac.arg(fac.ref(codLocal), true));
            var morsMapEndType = fac.app(fac.app(fac.app(fac.ref(ext.Ih.getRef()),
                                    fac.arg(fac.ref(obsMap), true)),
                            fac.arg(fac.ref(domLocal), true)),
                    fac.arg(fac.ref(codLocal), true));
            var morsMapType = fac.pi(List.of(fac.param(true, List.of(domLocal), typeObs),
                            fac.param(true, List.of(codLocal), typeObs), fac.param(true, List.of(nLocal), nType)),
                    morsMapEndType);

            var obsClause = fac.letClause(fac.refPattern(obs, null), null, obsTerm);
            var obsMapClause = fac.letClause(fac.refPattern(obsMap, null), null, obsMapTerm);
            var morsClause = fac.letClause(fac.refPattern(mors, null), morsType, morsTerm);
            var morsMapClause = fac.letClause(fac.refPattern(morsMap, null), morsMapType, morsMapTerm);
            return fac.letExpr(false, false, List.of(obsClause, obsMapClause, morsClause, morsMapClause), expression);
        }

        private ConcretePattern constructPattern(CoreExpression expr) {
            if (expr instanceof CoreSigmaExpression) {
                var link = ((CoreSigmaExpression) expr).getParameters();
                try {
                    link.getBinding().getName();
                } catch (IllegalStateException e) {
                    return fac.conPattern(ext.Unit.getRef());
                }
                List<CoreBinding> bindings = new ArrayList<>();
                while (link.hasNext()) {
                    bindings.add(link.getBinding());
                    link = link.getNext();
                }
                var res = constructPattern(bindings.get(bindings.size() - 1).getTypeExpr());
                for (int i = bindings.size() - 2; i >= 0; i--) {
                    var cur = constructPattern(bindings.get(i).getTypeExpr());
                    res = fac.conPattern(ext.Prod.getRef(), cur, res);
                }
                return res;
            }
            if (expr instanceof CoreReferenceExpression) {
                var name = ((CoreReferenceExpression) expr).getBinding().getName();
                var type = expr.computeType();
                if (type instanceof CoreUniverseExpression) {
                    int num = nh.obsNames.indexOf(name);
                    return fac.conPattern(ext.TParam.getRef(), fac.numberPattern(num));
                }
            }
            return null;
        }

        public ConcreteExpression construct(CoreExpression expr) {
            if (expr instanceof CoreSigmaExpression) {
                var link = ((CoreSigmaExpression) expr).getParameters();
                try {
                    link.getBinding().getName();
                } catch (IllegalStateException e) {
                    return unitT();
                }
                List<CoreBinding> bindings = new ArrayList<>();
                while (link.hasNext()) {
                    bindings.add(link.getBinding());
                    link = link.getNext();
                }
                var res = construct(bindings.get(bindings.size() - 1).getTypeExpr());
                for (int i = bindings.size() - 2; i >= 0; i--) {
                    var cur = construct(bindings.get(i).getTypeExpr());
                    res = prodT(cur, res);
                }
                return res;
            }
            if (expr instanceof CoreReferenceExpression) {
                var name = ((CoreReferenceExpression) expr).getBinding().getName();
                if (name.equals(var)) return var();
                var type = expr.computeType();
                if (type instanceof CorePiExpression) {
                    var dom = ((CorePiExpression) type).getParameters().getTypeExpr();
                    var cod = ((CorePiExpression) type).getCodomain();
                    return param(construct(cod), nh.morsOldNames.get(new Pair<>(dom.toString(), cod.toString())).indexOf(name));
                }
                if (type instanceof CoreUniverseExpression) {
                    return paramT(nh.obsNames.indexOf(name));
                }
            }
            if (expr instanceof CoreTupleExpression) {
                var fields = ((CoreTupleExpression) expr).getFields();
                if (fields.size() == 0) {
                    return unit();
                }
                var res = construct(fields.get(fields.size() - 1));
                for (int i = fields.size() - 2; i >= 0; i--) {
                    var cur = construct(fields.get(i));
                    res = tuple(cur, res);
                }
                return res;
            }
            if (expr instanceof CoreLamExpression) {
                var param = ((CoreLamExpression) expr).getParameters();
                var body = ((CoreLamExpression) expr).getBody();
                ctx = construct(param.getTypeExpr());
                var = param.getBinding().getName();
                return construct(body);
            }
            if (expr instanceof CoreProjExpression) {
                var type = ((CoreProjExpression) expr).getExpression().computeType();
                var link = ((CoreSigmaExpression) type).getParameters();
                int n = 0;
                while (link.hasNext()) {
                    n++;
                    link = link.getNext();
                }
                var term = construct(((CoreProjExpression) expr).getExpression());
                int ind = ((CoreProjExpression) expr).getField();
                boolean last = n == ind + 1;
                while (ind > 0) {
                    term = proj2(term);
                    ind--;
                }
                return last ? term : proj1(term);
            }
            return null;
        }

    }


    private static class TypesTranslator {
        List<String> names = new ArrayList<>();
        Map<String, ConcreteExpression> myContext = new HashMap<>();
        Map<String, ArendRef> refs = new HashMap<>();
        Map<String, CoreExpression> oldRefs = new HashMap<>();
        ConcreteFactory fac;

        public TypesTranslator(ConcreteFactory fac) {
            this.fac = fac;
        }

        public List<ConcreteParameter> generateParams() {
            return refs.values().stream()
                    .collect(Collectors.groupingBy(x -> myContext.get(x.getRefName()).toString(), Collectors.toList()))
                    .values().stream().map(x -> fac.param(true, x, myContext.get(x.get(0).getRefName()))).collect(Collectors.toList())
                    .stream().sorted(Comparator.comparingInt(x -> names.indexOf(x.getRefList().get(0).getRefName())))
                    .collect(Collectors.toList());
        }

        public ConcreteExpression infer(CoreExpression expr) throws IllegalStateException {
            if (expr instanceof CoreFieldCallExpression) {
                String name = ((CoreFieldCallExpression) expr).getDefinition().getRef().getRefName();
                if (name.equals("Ob")) {
                    return fac.universe(null, null);
                }
                if (name.equals("apex")) {
                    return infer(((CoreFieldCallExpression) expr).getArgument());
                }
                if (name.equals("terminal")) {
                    return fac.sigma();
                }
            }
            if (expr instanceof CoreAppExpression) {
                if (((CoreAppExpression) expr).getFunction() instanceof CoreAppExpression) {
                    var func = ((CoreAppExpression) ((CoreAppExpression) expr).getFunction()).getFunction();
                    if (func instanceof CoreFieldCallExpression) {
                        String name = ((CoreFieldCallExpression) func).getDefinition().getRef().getRefName();
                        var arg1 = ((CoreAppExpression) ((CoreAppExpression) expr).getFunction()).getArgument();
                        var arg2 = ((CoreAppExpression) expr).getArgument();
                        if (name.equals("Hom")) {
                            return fac.pi(List.of(fac.param(true, infer(arg1))), infer(arg2));
                        }
                        if (name.equals("Bprod")) {
                            return fac.sigma(fac.param(true, infer(arg1)), fac.param(true, infer(arg2)));
                        }
                    }
                }
            }
            if (expr instanceof CoreReferenceExpression) {
                var name = ((CoreReferenceExpression) expr).getBinding().getName();
                return fac.ref(refs.get(name));
            }
            throw new IllegalStateException();
        }

        public void translateContext(@NotNull List<CoreBinding> all) {
            for (var cb : all) {
                var type = cb.getTypeExpr();
                var name = cb.getName();
                try {
                    var translatedType = infer(type);
                    names.add(name);
                    myContext.put(name, translatedType);
                    refs.put(name, fac.local(name));
                    oldRefs.put(name, cb.makeReference());
                } catch (IllegalStateException ignored) {
                }
            }
        }
    }


    @Override
    public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        ConcreteFactory fac = ext.factory.withData(contextData.getMarker());
        List<? extends ConcreteArgument> args = contextData.getArguments();
        var context = typechecker.getFreeBindingsList();
        var translator = new TypesTranslator(fac);
        translator.translateContext(context);
        var expType = translator.infer(contextData.getExpectedType());
        var params = translator.generateParams();
        var finalExpType = typechecker.typecheck(fac.pi(params, expType), null).getExpression();
        var lam = typechecker.typecheck(args.get(0).getExpression(), finalExpType).getExpression();
        var nh = new NamesHolder(translator);
        lam = nh.set(lam, finalExpType, params);
        var ttf = new TypeTermFactory(ext, fac, nh);
        var constructed = ttf.construct(lam);
        var result = ttf.applyI(constructed);
        var withMaps = ttf.addParameterMaps(result);
        return typechecker.typecheck(withMaps, contextData.getExpectedType());
    }
}









