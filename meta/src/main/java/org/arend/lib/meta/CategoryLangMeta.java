package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.concrete.pattern.ConcretePattern;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.CoreClassField;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreDataDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;

import java.util.*;
import java.util.stream.Collectors;


public class CategoryLangMeta extends BaseMetaDefinition {
    private final StdExtension ext;
    private ConcreteFactory fac;
    ExpressionTypechecker typechecker;
    ConcreteSourceNode marker;
    BindingsManager bindingsManager;

    @Dependency(module = "CategoryLanguage.Cartesian", name = "Type")
    public CoreDataDefinition Type;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "Type.TParam")
    public CoreConstructor TParam;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "Type.Prod")
    public CoreConstructor Prod;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "Type.Unit")
    public CoreConstructor Unit;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "Term.Tuple")
    public CoreConstructor Tuple;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "Term.unit")
    public CoreConstructor unit;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "Term.Proj1")
    public CoreConstructor Proj1;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "Term.Proj2")
    public CoreConstructor Proj2;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "Term.Var")
    public CoreConstructor Var;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "Term.Param")
    public CoreConstructor Param;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "IT")
    public CoreFunctionDefinition IT;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "IC")
    public CoreFunctionDefinition IC;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "I")
    public CoreFunctionDefinition I;
    @Dependency(module = "CategoryLanguage.Cartesian", name = "Ih")
    public CoreFunctionDefinition Ih;

    @Dependency(module = "Category", name = "Precat.Ob")
    public CoreClassField catOb;
    @Dependency(module = "Category", name = "Precat.Hom")
    public CoreClassField catHom;
    @Dependency(module = "Category.Limit", name = "CartesianPrecat.terminal")
    public CoreClassField terminal;
    @Dependency(module = "Category.Limit", name = "CartesianPrecat.Bprod")
    public CoreClassField Bprod;
    @Dependency(module = "Category.Limit", name = "Product.apex")
    public CoreClassField apex;


    public boolean compare(CoreExpression value, CoreExpression element) {
        if (value == null || element == null) return value == element;
        return typechecker != null ? Utils.safeCompare(typechecker, value, element, CMP.EQ, marker, false, true) : value.compare(element, CMP.EQ);
    }

    public CategoryLangMeta(StdExtension ext) {
        this.ext = ext;
    }

    @Override
    public boolean[] argumentExplicitness() {
        return new boolean[]{true};
    }

    private class BindingsManager {
        private final List<CoreExpression> oldBindings;
        private Values<CoreExpression> newBindings;
        private Values<CoreExpression> obsValues;
        private List<Pair<Pair<CoreExpression, CoreExpression>, Values<CoreExpression>>> morsValuesList = new ArrayList<>();

        public BindingsManager(List<CoreExpression> bindings) {
            oldBindings = bindings;
        }

        public List<Pair<Pair<CoreExpression, CoreExpression>, Values<CoreExpression>>> getMorsLists() {
            return morsValuesList;
        }

        public int getMorIndex(CoreExpression dom, CoreExpression cod, CoreExpression var) {
            return getMorsLists().stream()
                    .filter(x -> compare(x.proj1.proj1, dom) && compare(x.proj1.proj2, cod))
                    .map(x -> x.proj2).collect(Collectors.toList()).get(0).getIndex(var);
        }

        public int getObIndex(CoreExpression var) {
            return obsValues.getIndex(var);
        }

        public CoreExpression newToOld(CoreExpression expression) {
            return oldBindings.get(newBindings.getIndex(expression));
        }

        private Pair<CoreExpression, CoreExpression> inferDomCod(CoreExpression expr) {
            if (expr instanceof CorePiExpression) {
                var dom = ((CorePiExpression) expr).getParameters().getTypeExpr();
                var cod = ((CorePiExpression) expr).getCodomain();
                return new Pair<>(dom, cod);
            }
            return null;
        }

        private Values<CoreExpression> listToValues(List<CoreExpression> l) {
            var res = new Values<CoreExpression>(typechecker, marker);
            l.forEach(res::addValue);
            return res;
        }

        public CoreExpression set(CoreExpression lam) {
            newBindings = new Values<>(typechecker, marker);
            for (int i = 0; i < oldBindings.size(); i++) {
                newBindings.addValue(((CoreLamExpression) lam).getParameters().getBinding().makeReference());
                lam = ((CoreLamExpression) lam).getBody();
            }
            obsValues = listToValues(newBindings.getValues().stream()
                    .filter(x -> (x.computeType() instanceof CoreUniverseExpression)).collect(Collectors.toList()));
            var typesValues = new Values<CoreExpression>(typechecker, marker);
            newBindings.getValues().forEach(b -> typesValues.addValue(b.computeType()));
            morsValuesList = newBindings.getValues().stream()
                    .collect(Collectors.groupingBy(x -> typesValues.getIndex(x.computeType()))).entrySet().stream()
                    .map(x -> new Pair<>(inferDomCod(typesValues.getValue(x.getKey())), listToValues(x.getValue())))
                    .filter(x -> x.proj1 != null).collect(Collectors.toList());
            return lam;
        }
    }

    private class TypeTermFactory {
        ArendRef obs;
        ArendRef obsMap;
        ArendRef mors;
        ArendRef morsMap;

        ConcreteExpression ctx;
        CoreExpression var;


        public TypeTermFactory() {
            obs = fac.local("obs");
            obsMap = fac.local("obsMap");
            mors = fac.local("mors");
            morsMap = fac.local("morsMap");
        }

        public ConcreteExpression paramT(int i) {
            return fac.app(fac.ref(TParam.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.number(i), true));
        }

        public ConcreteExpression prodT(ConcreteExpression a, ConcreteExpression b) {
            return fac.app(fac.ref(Prod.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(a, true), fac.arg(b, true));
        }

        public ConcreteExpression unitT() {
            return fac.app(fac.ref(Unit.getRef()),
                    fac.arg(fac.ref(obs), false));
        }

        public ConcreteExpression tuple(ConcreteExpression a, ConcreteExpression b) {
            return fac.app(fac.ref(Tuple.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false),
                    fac.arg(a, true), fac.arg(b, true));
        }

        public ConcreteExpression unit() {
            return fac.app(fac.ref(unit.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false));
        }

        public ConcreteExpression proj1(ConcreteExpression t) {
            return fac.app(fac.ref(Proj1.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false),
                    fac.arg(t, true));
        }

        public ConcreteExpression proj2(ConcreteExpression t) {
            return fac.app(fac.ref(Proj2.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false),
                    fac.arg(t, true));
        }

        public ConcreteExpression param(ConcreteExpression t, ConcreteExpression T, int i) {
            return fac.app(fac.ref(Param.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false),
                    fac.arg(T, false), fac.arg(fac.number(i), true), fac.arg(t, true));
        }

        public ConcreteExpression var() {
            return fac.app(fac.ref(Var.getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(ctx, false),
                    fac.arg(ctx, false), fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true));
        }

        public ConcreteExpression applyI(ConcreteExpression term) {
            return fac.app(fac.ref(I.getRef()), fac.arg(fac.ref(obsMap), true),
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
            var all = bindingsManager.getMorsLists();
            for (var p : all) {
                var domExpr = p.proj1.proj1;
                var codExpr = p.proj1.proj2;
                var params = p.proj2;
                var domPat = constructPattern(domExpr);
                var codPat = constructPattern(codExpr);
                ConcreteClause clause;
                if (onlySet) {
                    clause = fac.clause(List.of(domPat, codPat),
                            fac.app(fac.ref(ext.prelude.getFin().getRef()),
                                    fac.arg(fac.number(params.getValues().size()), true)));
                } else {
                    var nLocal = fac.local("n");
                    var morsArgs = params.getValues().stream().map(bindingsManager::newToOld)
                            .map(x -> fac.core(x.computeTyped())).collect(Collectors.toList());
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
                    fac.arg(fac.number(bindingsManager.obsValues.getValues().size()), true));
            var obsArgs = bindingsManager.obsValues.getValues().stream().map(bindingsManager::newToOld)
                    .map(x -> fac.core(x.computeTyped())).collect(Collectors.toList());
            var obsMapTerm = listMap(obsArgs);

            var morsTerm = morsLam(true);
            var morsMapTerm = morsLam(false);

            var typeObs = fac.app(fac.ref(Type.getRef()), fac.arg(fac.ref(obs), true));

            var domLocal = fac.local("dom");
            var codLocal = fac.local("cod");
            var morsType = fac.pi(List.of(fac.param(true, List.of(domLocal), typeObs),
                    fac.param(true, List.of(codLocal), typeObs)), fac.universe(null, fac.numLevel(0)));

            domLocal = fac.local("dom");
            codLocal = fac.local("cod");
            var nLocal = fac.local("n");
            var nType = fac.app(fac.app(fac.ref(mors), fac.arg(fac.ref(domLocal), true)),
                    fac.arg(fac.ref(codLocal), true));
            var morsMapEndType = fac.app(fac.app(fac.app(fac.ref(Ih.getRef()),
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
                    return fac.conPattern(Unit.getRef());
                }
                List<CoreBinding> bindings = new ArrayList<>();
                while (link.hasNext()) {
                    bindings.add(link.getBinding());
                    link = link.getNext();
                }
                var res = constructPattern(bindings.get(bindings.size() - 1).getTypeExpr());
                for (int i = bindings.size() - 2; i >= 0; i--) {
                    var cur = constructPattern(bindings.get(i).getTypeExpr());
                    res = fac.conPattern(Prod.getRef(), cur, res);
                }
                return res;
            }
            if (expr instanceof CoreReferenceExpression) {
                var type = expr.computeType();
                if (type instanceof CoreUniverseExpression) {
                    int num = bindingsManager.getObIndex(expr);
                    return fac.conPattern(TParam.getRef(), fac.numberPattern(num));
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
            if (expr instanceof CoreAppExpression) {
                var fun = ((CoreAppExpression) expr).getFunction();
                var arg = ((CoreAppExpression) expr).getArgument();
                var type = fun.computeType();
                if (type instanceof CorePiExpression) {
                    var dom = ((CorePiExpression) type).getParameters().getTypeExpr();
                    var cod = ((CorePiExpression) type).getCodomain();
                    return param(construct(arg), construct(cod), bindingsManager.getMorIndex(dom, cod, fun));
                }
            }
            if (expr instanceof CoreReferenceExpression) {
                if (compare(expr, var)) return var();
                var type = expr.computeType();
                if (type instanceof CoreUniverseExpression) {
                    return paramT(bindingsManager.getObIndex(expr));
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
                var = param.getBinding().makeReference();
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

    private class TypesTranslator {
        Map<Integer, String> names = new HashMap<>();
        Map<String, ConcreteExpression> myContext = new HashMap<>();
        Map<String, ArendRef> refs = new HashMap<>();
        Map<String, CoreExpression> oldRefs = new HashMap<>();
        Values<UncheckedExpression> values;

        public TypesTranslator() {
            values = new Values<>(typechecker, marker);
        }

        private int getIndexByName(String name) {
            return names.entrySet().stream().filter(x -> x.getValue().equals(name))
                    .map(Map.Entry::getKey).collect(Collectors.toList()).get(0);
        }

        public List<ConcreteParameter> generateParams() {
            return refs.values().stream()
                    .collect(Collectors.groupingBy(x -> myContext.get(x.getRefName()).toString(), Collectors.toList()))
                    .values().stream().map(x -> fac.param(true, x, myContext.get(x.get(0).getRefName()))).collect(Collectors.toList())
                    .stream().sorted(Comparator.comparingInt(x -> getIndexByName(x.getRefList().get(0).getRefName())))
                    .collect(Collectors.toList());
        }

        public ConcreteExpression infer(CoreExpression expr) throws IllegalStateException {
            if (values.getIndex(expr) != -1) {
                String name = names.get(values.getIndex(expr));
                return fac.ref(refs.get(name));
            }
            if (expr instanceof CoreFieldCallExpression) {
                var classField = ((CoreFieldCallExpression) expr).getDefinition();
                if (classField == catOb) {
                    return fac.universe(null, null);
                }
                if (classField == apex) {
                    return infer(((CoreFieldCallExpression) expr).getArgument());
                }
                if (classField == terminal) {
                    return fac.sigma();
                }
            }
            if (expr instanceof CoreAppExpression) {
                if (((CoreAppExpression) expr).getFunction() instanceof CoreAppExpression) {
                    var func = ((CoreAppExpression) ((CoreAppExpression) expr).getFunction()).getFunction();
                    if (func instanceof CoreFieldCallExpression) {
                        var classField = ((CoreFieldCallExpression) func).getDefinition();
                        var arg1 = ((CoreAppExpression) ((CoreAppExpression) expr).getFunction()).getArgument();
                        var arg2 = ((CoreAppExpression) expr).getArgument();
                        if (classField == catHom) {
                            return fac.pi(List.of(fac.param(true, infer(arg1))), infer(arg2));
                        }
                        if (classField == Bprod) {
                            return fac.sigma(fac.param(true, infer(arg1)), fac.param(true, infer(arg2)));
                        }
                    }
                }
            }
            throw new IllegalStateException();
        }

        private String generateName(CoreExpression expr) {
            return expr.toString().replace(" ", "_");
        }

        public void translateContext(@NotNull List<TypedExpression> all) {
            for (var te : all) {
                var expr = te.getExpression();
                var type = te.getType();
                try {
                    var translatedType = infer(type);
                    values.addValue(expr);
                    String name = generateName(expr);
                    names.put(values.getIndex(expr), name);
                    myContext.put(name, translatedType);
                    refs.put(name, fac.local(name));
                    oldRefs.put(name, expr);
                } catch (IllegalStateException ignored) {
                }
            }
        }
    }

    @Override
    public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        fac = ext.factory.withData(contextData.getMarker());
        this.typechecker = typechecker;
        marker = contextData.getMarker();
        List<? extends ConcreteArgument> args = contextData.getArguments();
        var context = args.subList(0, args.size() - 1).stream()
                .map(x -> typechecker.typecheck(x.getExpression(), null)).collect(Collectors.toList());
        var translator = new TypesTranslator();
        translator.translateContext(context);
        var expType = translator.infer(contextData.getExpectedType());
        var params = translator.generateParams();
        var finalExpType = typechecker.typecheck(fac.pi(params, expType), null).getExpression();
        var lam = typechecker.typecheck(args.get(args.size() - 1).getExpression(), finalExpType).getExpression();
        var bindings = params.stream()
                .flatMap(concreteParameter -> concreteParameter.getRefList().stream()
                        .map(x -> translator.oldRefs.get(x.getRefName()))).collect(Collectors.toList());
        bindingsManager = new BindingsManager(bindings);
        lam = bindingsManager.set(lam);
        var ttf = new TypeTermFactory();
        var constructed = ttf.construct(lam);
        var result = ttf.applyI(constructed);
        var withMaps = ttf.addParameterMaps(result);
        return typechecker.typecheck(withMaps, contextData.getExpectedType());
    }
}









