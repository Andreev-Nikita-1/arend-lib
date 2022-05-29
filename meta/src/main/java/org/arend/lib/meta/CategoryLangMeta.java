package org.arend.lib.meta;

import org.arend.ext.concrete.ConcreteClause;
import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.*;
import org.arend.ext.concrete.pattern.ConcretePattern;
import org.arend.ext.core.body.CoreElimClause;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.definition.*;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.CMP;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.error.GeneralError;
import org.arend.ext.error.LocalError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.*;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Utils;
import org.arend.lib.util.Values;
import org.jetbrains.annotations.NotNull;

import java.lang.instrument.ClassDefinition;
import java.util.*;
import java.util.stream.Collectors;


public class CategoryLangMeta extends BaseMetaDefinition {
    private final StdExtension ext;
    private ConcreteFactory fac;
    ExpressionTypechecker typechecker;
    ConcreteSourceNode marker;


    public final CartesianFieldsProvider cfp = new CartesianFieldsProvider();
    public final CartesianClosedFieldsProvider ccfp = new CartesianClosedFieldsProvider();


    @Dependency(module = "Category.Limit", name = "CartesianPrecat")
    public CoreClassDefinition CartesianPrecat;
    @Dependency(module = "Category.Limit", name = "CartesianClosedPrecat")
    public CoreClassDefinition CartesianClosedPrecat;

    interface FieldsProvider {
        public CoreDataDefinition getType();

        public CoreConstructor getTParam();

        public CoreConstructor getProd();

        public CoreConstructor getUnitT();

        public CoreConstructor getProj1();

        public CoreConstructor getProj2();

        public CoreConstructor getVar();

        public CoreConstructor getParam();

        public CoreFunctionDefinition getIT();

        public CoreFunctionDefinition getI();

        public CoreFunctionDefinition getIh();

        public CoreFunctionDefinition getLemma();

        public CoreDataDefinition getMor();

        public CoreConstructor getId();

        public CoreClassField getTerminal();

        public CoreClassField getBprod();

        public CoreClassField getApex();

        public CoreConstructor getMParam();

        public CoreConstructor getComp();

        public CoreConstructor getTerminalMap();

        public CoreConstructor getTupleMap();


        public CoreClassField getProj();

        public CoreConstructor getProj1Map();

        public CoreConstructor getProj2Map();

        public CoreFunctionDefinition getIM();

        public CoreClassField getCatOb();

        public CoreClassField getCatHom();

        public CoreConstructor getTuple();

        public CoreConstructor getUnit();

        public CoreClassField getIdCat();

        public CoreClassField getTupleMapCat();

        default public CoreConstructor getArr() {
            return null;
        }

        default public CoreConstructor getApp() {
            return null;
        }

        default public CoreConstructor getLam() {
            return null;
        }

        default public CoreConstructor getLamMap() {
            return null;
        }

        default public CoreConstructor getEvMap() {
            return null;
        }

        default public CoreClassField getExp() {
            return null;
        }
    }

    static class CartesianFieldsProvider implements FieldsProvider {
        public CoreDataDefinition getType() {
            return Type;
        }

        public CoreConstructor getTParam() {
            return TParam;
        }

        public CoreConstructor getProd() {
            return Prod;
        }

        public CoreConstructor getUnitT() {
            return UnitT;
        }

        public CoreConstructor getUnit() {
            return unit;
        }

        public CoreConstructor getProj1() {
            return Proj1;
        }

        public CoreConstructor getProj2() {
            return Proj2;
        }

        public CoreConstructor getVar() {
            return Var;
        }

        public CoreConstructor getParam() {
            return Param;
        }

        public CoreFunctionDefinition getIT() {
            return IT;
        }

        public CoreFunctionDefinition getI() {
            return I;
        }

        public CoreFunctionDefinition getIh() {
            return Ih;
        }

        public CoreFunctionDefinition getLemma() {
            return lemma;
        }

        public CoreDataDefinition getMor() {
            return Mor;
        }

        public CoreConstructor getId() {
            return Id;
        }

        public CoreClassField getIdCat() {
            return id;
        }

        public CoreClassField getTerminal() {
            return terminal;
        }

        public CoreClassField getBprod() {
            return Bprod;
        }

        public CoreClassField getApex() {
            return apex;
        }

        public CoreConstructor getMParam() {
            return MParam;
        }

        public CoreConstructor getComp() {
            return Comp;
        }

        public CoreConstructor getTerminalMap() {
            return TerminalMap;
        }

        public CoreConstructor getTupleMap() {
            return TupleMap;
        }

        public CoreClassField getTupleMapCat() {
            return tupleMap;
        }

        public CoreClassField getProj() {
            return proj;
        }

        public CoreConstructor getProj1Map() {
            return Proj1Map;
        }

        public CoreConstructor getProj2Map() {
            return Proj2Map;
        }

        public CoreFunctionDefinition getIM() {
            return IM;
        }

        public CoreClassField getCatOb() {
            return catOb;
        }

        public CoreClassField getCatHom() {
            return catHom;
        }

        public CoreConstructor getTuple() {
            return Tuple;
        }

        @Dependency(module = "CategoryLanguage.Cartesian", name = "Type")
        public CoreDataDefinition Type;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Type.TParam")
        public CoreConstructor TParam;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Type.Prod")
        public CoreConstructor Prod;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Type.Unit")
        public CoreConstructor UnitT;
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
        @Dependency(module = "CategoryLanguage.Cartesian", name = "I")
        public CoreFunctionDefinition I;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Ih")
        public CoreFunctionDefinition Ih;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "lemma")
        public CoreFunctionDefinition lemma;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Mor")
        public CoreDataDefinition Mor;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Mor.Id")
        public CoreConstructor Id;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Mor.MParam")
        public CoreConstructor MParam;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Mor.Comp")
        public CoreConstructor Comp;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Mor.TerminalMap")
        public CoreConstructor TerminalMap;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Mor.TupleMap")
        public CoreConstructor TupleMap;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Mor.Proj1Map")
        public CoreConstructor Proj1Map;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "Mor.Proj2Map")
        public CoreConstructor Proj2Map;
        @Dependency(module = "CategoryLanguage.Cartesian", name = "IM")
        public CoreFunctionDefinition IM;


        @Dependency(module = "Category", name = "Precat.Ob")
        public CoreClassField catOb;
        @Dependency(module = "Category", name = "Precat.Hom")
        public CoreClassField catHom;
        @Dependency(module = "Category", name = "Precat.id")
        public CoreClassField id;
        @Dependency(module = "Category.Limit", name = "CartesianPrecat.terminal")
        public CoreClassField terminal;
        @Dependency(module = "Category.Limit", name = "CartesianPrecat.Bprod")
        public CoreClassField Bprod;
        @Dependency(module = "Category.Limit", name = "Product.apex")
        public CoreClassField apex;
        @Dependency(module = "Category.Limit", name = "Product.tupleMap")
        public CoreClassField tupleMap;
        @Dependency(module = "Category.Limit", name = "Product.proj")
        public CoreClassField proj;

    }

    static class CartesianClosedFieldsProvider implements FieldsProvider {
        public CoreDataDefinition getType() {
            return Type;
        }

        public CoreConstructor getTParam() {
            return TParam;
        }

        public CoreConstructor getProd() {
            return Prod;
        }

        public CoreConstructor getUnitT() {
            return UnitT;
        }

        public CoreConstructor getUnit() {
            return unit;
        }

        public CoreConstructor getProj1() {
            return Proj1;
        }

        public CoreConstructor getProj2() {
            return Proj2;
        }

        public CoreConstructor getVar() {
            return Var;
        }

        public CoreConstructor getParam() {
            return Param;
        }

        public CoreFunctionDefinition getIT() {
            return IT;
        }

        public CoreFunctionDefinition getI() {
            return I;
        }

        public CoreFunctionDefinition getIh() {
            return Ih;
        }

        public CoreFunctionDefinition getLemma() {
            return lemma;
        }

        public CoreDataDefinition getMor() {
            return Mor;
        }

        public CoreConstructor getId() {
            return Id;
        }

        public CoreClassField getIdCat() {
            return id;
        }

        public CoreClassField getTerminal() {
            return terminal;
        }

        public CoreClassField getBprod() {
            return Bprod;
        }

        public CoreClassField getApex() {
            return apex;
        }

        public CoreConstructor getMParam() {
            return MParam;
        }

        public CoreConstructor getComp() {
            return Comp;
        }

        public CoreConstructor getTerminalMap() {
            return TerminalMap;
        }

        public CoreConstructor getTupleMap() {
            return TupleMap;
        }

        public CoreClassField getTupleMapCat() {
            return tupleMap;
        }

        public CoreClassField getProj() {
            return proj;
        }

        public CoreConstructor getProj1Map() {
            return Proj1Map;
        }

        public CoreConstructor getProj2Map() {
            return Proj2Map;
        }

        public CoreFunctionDefinition getIM() {
            return IM;
        }

        public CoreClassField getCatOb() {
            return catOb;
        }

        public CoreClassField getCatHom() {
            return catHom;
        }

        public CoreConstructor getTuple() {
            return Tuple;
        }

        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Type")
        public CoreDataDefinition Type;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Type.TParam")
        public CoreConstructor TParam;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Type.Prod")
        public CoreConstructor Prod;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Type.Unit")
        public CoreConstructor UnitT;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Type.Arr")
        public CoreConstructor Arr;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Term.Tuple")
        public CoreConstructor Tuple;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Term.unit")
        public CoreConstructor unit;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Term.Proj1")
        public CoreConstructor Proj1;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Term.Proj2")
        public CoreConstructor Proj2;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Term.Var")
        public CoreConstructor Var;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Term.Param")
        public CoreConstructor Param;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Term.App")
        public CoreConstructor App;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Term.Lam")
        public CoreConstructor Lam;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "IT")
        public CoreFunctionDefinition IT;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "I")
        public CoreFunctionDefinition I;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Ih")
        public CoreFunctionDefinition Ih;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "lemma")
        public CoreFunctionDefinition lemma;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Mor")
        public CoreDataDefinition Mor;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Mor.Id")
        public CoreConstructor Id;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Mor.MParam")
        public CoreConstructor MParam;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Mor.Comp")
        public CoreConstructor Comp;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Mor.TerminalMap")
        public CoreConstructor TerminalMap;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Mor.TupleMap")
        public CoreConstructor TupleMap;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Mor.Proj1Map")
        public CoreConstructor Proj1Map;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Mor.Proj2Map")
        public CoreConstructor Proj2Map;

        public CoreConstructor getArr() {
            return Arr;
        }

        public CoreConstructor getApp() {
            return App;
        }

        public CoreConstructor getLam() {
            return Lam;
        }

        public CoreConstructor getLamMap() {
            return LamMap;
        }

        public CoreConstructor getEvMap() {
            return EvMap;
        }

        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Mor.LamMap")
        public CoreConstructor LamMap;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "Mor.EvMap")
        public CoreConstructor EvMap;
        @Dependency(module = "CategoryLanguage.CartesianClosed", name = "IM")
        public CoreFunctionDefinition IM;


        @Dependency(module = "Category", name = "Precat.Ob")
        public CoreClassField catOb;
        @Dependency(module = "Category", name = "Precat.Hom")
        public CoreClassField catHom;
        @Dependency(module = "Category", name = "Precat.id")
        public CoreClassField id;
        @Dependency(module = "Category.Limit", name = "CartesianPrecat.terminal")
        public CoreClassField terminal;
        @Dependency(module = "Category.Limit", name = "CartesianPrecat.Bprod")
        public CoreClassField Bprod;
        @Dependency(module = "Category.Limit", name = "Product.apex")
        public CoreClassField apex;
        @Dependency(module = "Category.Limit", name = "Product.tupleMap")
        public CoreClassField tupleMap;
        @Dependency(module = "Category.Limit", name = "Product.proj")
        public CoreClassField proj;

        public CoreClassField getExp() {
            return exp;
        }

        @Dependency(module = "Category.Limit", name = "CartesianClosedPrecat.exp")
        public CoreClassField exp;
    }


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

        public Values<CoreExpression> obsValues = new Values<>(typechecker, marker);
        private List<Pair<Pair<CoreExpression, CoreExpression>, Values<CoreExpression>>> morsValuesList = new ArrayList<>();

        private Optional<Values<CoreExpression>> getMorsValues(CoreExpression dom, CoreExpression cod) {
            var v = morsValuesList.stream()
                    .filter(x -> compare(x.proj1.proj1, dom) && compare(x.proj1.proj2, cod))
                    .map(x -> x.proj2).collect(Collectors.toList());
            if (v.size() > 0) {
                return Optional.of(v.get(0));
            }
            return Optional.empty();
        }

        public int addMor(CoreExpression dom, CoreExpression cod, CoreExpression m) {
            var o = getMorsValues(dom, cod);
            if (o.isPresent()) {
                return o.get().addValue(m);
            }
            morsValuesList.add(new Pair<>(new Pair<>(dom, cod), new Values<>(typechecker, marker)));
            return morsValuesList.get(morsValuesList.size() - 1).proj2.addValue(m);
        }

        private Values<CoreExpression> oldBindings;
        private Values<CoreExpression> newBindings;
//        public Values<CoreExpression> obsValuesNew = new Values<>(typechecker, marker);
        private List<Pair<Pair<CoreExpression, CoreExpression>, Values<CoreExpression>>> newMorsValuesList = new ArrayList<>();


        public int getMorIndexNew(CoreExpression dom, CoreExpression cod, CoreExpression var) {
            var list = newMorsValuesList.stream()
                    .filter(x -> compare(x.proj1.proj1, dom) && compare(x.proj1.proj2, cod))
                    .map(x -> x.proj2).collect(Collectors.toList());
            if (list.isEmpty()) {
                return -1;
            }
            return list.get(0).getIndex(var);
        }

        public int getObIndex(CoreExpression var) {
            return obsValues.getIndex(var);
        }

//        public int getObIndexNew(CoreExpression var) {
//            return obsValuesNew.getIndex(var);
//        }

        public CoreExpression newToOld(CoreExpression expression) {
            return oldBindings.getValue(newBindings.getIndex(expression));
        }

        private Pair<CoreExpression, CoreExpression> inferDomCod(CoreExpression expr) {
            if (expr instanceof CoreAppExpression) {
                var dom = ((CoreAppExpression) ((CoreAppExpression) expr).getFunction()).getArgument();
                var cod = ((CoreAppExpression) expr).getArgument();
                return new Pair<>(dom, cod);
            }
            return null;
        }

        private Pair<CoreExpression, CoreExpression> inferDomCodNew(CoreExpression expr) {
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

        public CoreExpression set(List<CoreExpression> bindings, CoreExpression lam) {
            oldBindings = listToValues(bindings);
            newBindings = new Values<>(typechecker, marker);
            if (lam != null) {
                for (int i = 0; i < oldBindings.getValues().size(); i++) {
                    newBindings.addValue(((CoreLamExpression) lam).getParameters().getBinding().makeReference());
                    lam = ((CoreLamExpression) lam).getBody();
                }
            }
            List<CoreExpression> obsValues0 = new ArrayList<>();
            List<CoreExpression> obsValuesNew0 = new ArrayList<>();
            for (int i = 0; i < newBindings.getValues().size(); i++) {
                if (newBindings.getValues().get(i).computeType() instanceof CoreUniverseExpression) {
                    obsValues0.add(oldBindings.getValue(i));
                    obsValuesNew0.add(newBindings.getValue(i));
                }
            }
            obsValues = listToValues(obsValues0);
//            obsValuesNew = listToValues(obsValuesNew0);

            var typesValues = new Values<CoreExpression>(typechecker, marker);
            oldBindings.getValues().forEach(b -> typesValues.addValue(b.computeType()));
            morsValuesList = oldBindings.getValues().stream()
                    .collect(Collectors.groupingBy(x -> typesValues.getIndex(x.computeType()))).entrySet().stream()
                    .map(x -> new Pair<>(inferDomCod(typesValues.getValue(x.getKey())), listToValues(x.getValue())))
                    .filter(x -> x.proj1 != null).collect(Collectors.toList());

            var typesValuesNew = new Values<CoreExpression>(typechecker, marker);
            newBindings.getValues().forEach(b -> typesValuesNew.addValue(b.computeType()));
            newMorsValuesList = newBindings.getValues().stream()
                    .collect(Collectors.groupingBy(x -> typesValuesNew.getIndex(x.computeType()))).entrySet().stream()
                    .map(x -> new Pair<>(inferDomCodNew(typesValuesNew.getValue(x.getKey())), listToValues(x.getValue())))
                    .filter(x -> x.proj1 != null).collect(Collectors.toList());
//            morsValuesList = newMorsValuesList.stream().map(x -> new Pair<>(x.proj1, listToValues(x.proj2.getValues().stream().map(this::newToOld).collect(Collectors.toList())))).collect(Collectors.toList());
            return lam;
        }
    }

    private class TypeTermFactory {
        ArendRef obs;
        ArendRef obsMap;
        ArendRef mors;
        ArendRef morsMap;

        List<ConcreteExpression> ctx = new ArrayList<>();
        Values<CoreExpression> vars = new Values<>(typechecker, marker);

        BindingsManager bm = new BindingsManager();
        FieldsProvider fp;

        boolean firstStep = true;

        public TypeTermFactory(FieldsProvider fp) {
            obs = fac.local("obs");
            obsMap = fac.local("obsMap");
            mors = fac.local("mors");
            morsMap = fac.local("morsMap");
            this.fp = fp;
        }

        private ConcreteExpression currentCtx() {
            if (ctx.size() == 1) {
                return ctx.get(0);
            }
            var res = ctx.get(0);
            for (int i = 1; i < ctx.size(); i++) {
                res = prodT(res, ctx.get(i));
            }
            return res;
        }

        private ConcreteExpression varFromCtx(int i) {
            if (ctx.size() == 1) {
                return var();
            }
            int j = ctx.size() - 1;
            var res = var();
            while (i < j) {
                res = proj1(res);
                j--;
            }
            return i == 0 ? res : proj2(res);
        }

        public ConcreteExpression Type() {
            return fac.app(fac.ref(fp.getType().getRef()), fac.arg(fac.ref(obs), true));
        }

        public ConcreteExpression Mor(ConcreteExpression dom, ConcreteExpression cod) {
            return fac.app(fac.ref(fp.getMor().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), true),
                    fac.arg(dom, true),
                    fac.arg(cod, true));
        }

        public ConcreteExpression paramT(int i) {
            return fac.app(fac.ref(fp.getTParam().getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.number(i), true));
        }

        public ConcreteExpression prodT(ConcreteExpression a, ConcreteExpression b) {
            return fac.app(fac.ref(fp.getProd().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(a, true),
                    fac.arg(b, true));
        }

        public ConcreteExpression arr(ConcreteExpression a, ConcreteExpression b) {
            return fac.app(fac.ref(fp.getArr().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(a, true),
                    fac.arg(b, true));
        }

        public ConcreteExpression unitT() {
            return fac.app(fac.ref(fp.getUnitT().getRef()),
                    fac.arg(fac.ref(obs), false));
        }

        public ConcreteExpression tuple(ConcreteExpression a, ConcreteExpression b) {
            return fac.app(fac.ref(fp.getTuple().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(currentCtx(), false),
                    fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                    fac.arg(a, true), fac.arg(b, true));
        }

        public ConcreteExpression unit(ConcreteExpression t) {
            return fac.app(fac.ref(fp.getUnit().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(currentCtx(), false),
                    fac.arg(t, false),
                    fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true)
            );
        }

        public ConcreteExpression proj1(ConcreteExpression t) {
            return fac.app(fac.ref(fp.getProj1().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(currentCtx(), false),
                    fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                    fac.arg(t, true));
        }

        public ConcreteExpression proj2(ConcreteExpression t) {
            return fac.app(fac.ref(fp.getProj2().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(currentCtx(), false),
                    fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                    fac.arg(t, true));
        }

        public ConcreteExpression param(ConcreteExpression t, ConcreteExpression T, int i) {
            return fac.app(fac.ref(fp.getParam().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(currentCtx(), false),
                    fac.arg(T, false),
                    fac.arg(fac.number(i), true),
                    fac.arg(t, true));
        }

        public ConcreteExpression var() {
            return fac.app(fac.ref(fp.getVar().getRef()),
                    fac.arg(fac.ref(obs), false), fac.arg(fac.ref(mors), false), fac.arg(currentCtx(), false),
                    fac.arg(currentCtx(), false), fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true));
        }

        public ConcreteExpression lam(ConcreteExpression t) {
            return fac.app(fac.ref(fp.getLam().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(currentCtx(), false),
                    fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                    fac.arg(t, true));
        }

        public ConcreteExpression app(ConcreteExpression t1, ConcreteExpression t2) {
            return fac.app(fac.ref(fp.getApp().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(currentCtx(), false),
                    fac.arg(t1, true), fac.arg(t2, true));
        }


        public ConcreteExpression id(ConcreteExpression dom) {
            return fac.app(fac.ref(fp.getId().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(dom, false),
                    fac.arg(dom, false),
                    fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true));
        }

        public ConcreteExpression paramM(ConcreteExpression dom, ConcreteExpression cod, int i) {
            return fac.app(fac.ref(fp.getMParam().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(dom, false),
                    fac.arg(cod, false),
                    fac.arg(fac.number(i), true));
        }

        public ConcreteExpression comp(ConcreteExpression dom, ConcreteExpression cod, ConcreteExpression mid,
                                       ConcreteExpression a, ConcreteExpression b) {
            return fac.app(fac.ref(fp.getComp().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(dom, false),
                    fac.arg(cod, false),
                    fac.arg(mid, false),
                    fac.arg(a, true),
                    fac.arg(b, true));
        }

        public ConcreteExpression terminalMap(ConcreteExpression dom) {
            return fac.app(fac.ref(fp.getTerminalMap().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(dom, false),
                    fac.arg(unitT(), false),
                    fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true));
        }

        public ConcreteExpression tupleMap(ConcreteExpression a, ConcreteExpression b) {
            return fac.app(fac.ref(fp.getTupleMap().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                    fac.arg(a, true),
                    fac.arg(b, true)
            );
        }

        public ConcreteExpression proj1Map(ConcreteExpression dom) {
            return fac.app(fac.ref(fp.getProj1Map().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(dom, false),
                    fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true)
            );
        }

        public ConcreteExpression proj2Map(ConcreteExpression dom) {
            return fac.app(fac.ref(fp.getProj2Map().getRef()),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(dom, false),
                    fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true)
            );
        }

        public ConcreteExpression applyI(ConcreteExpression term) {
            return fac.app(fac.ref(fp.getI().getRef()), fac.arg(fac.ref(obsMap), true),
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
            var all = bm.morsValuesList;
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
                    var morsArgs = params.getValues().stream()
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

        public ConcreteExpression addParameterMaps(ConcreteExpression expression, boolean eqMode) {
            var obsTerm = fac.app(fac.ref(ext.prelude.getFin().getRef()),
                    fac.arg(fac.number(bm.obsValues.getValues().size()), true));
            var obsArgs = bm.obsValues.getValues().stream()
                    .map(x -> fac.core(x.computeTyped())).collect(Collectors.toList());
            var obsMapTerm = listMap(obsArgs);

            var morsTerm = morsLam(true);
            var morsMapTerm = morsLam(false);

            var typeObs = fac.app(fac.ref(fp.getType().getRef()), fac.arg(fac.ref(obs), true));

            var domLocal = fac.local("dom");
            var codLocal = fac.local("cod");
            var morsType = fac.pi(List.of(fac.param(true, List.of(domLocal), typeObs),
                    fac.param(true, List.of(codLocal), typeObs)), fac.universe(null, fac.numLevel(0)));

            domLocal = fac.local("dom");
            codLocal = fac.local("cod");
            var nLocal = fac.local("n");
            var nType = fac.app(fac.app(fac.ref(mors), fac.arg(fac.ref(domLocal), true)),
                    fac.arg(fac.ref(codLocal), true));
            var morsMapEndType = fac.app(fac.app(fac.app(fac.ref(fp.getIh().getRef()),
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
            if (bm.obsValues.getIndex(expr) != -1) {
                int num = bm.obsValues.getIndex(expr);
                return fac.conPattern(fp.getTParam().getRef(), fac.numberPattern(num));
            }
            if (expr instanceof CoreFieldCallExpression) {
                var classField = ((CoreFieldCallExpression) expr).getDefinition();
                if (classField == fp.getApex()) {
                    return constructPattern(((CoreFieldCallExpression) expr).getArgument());
                }
                if (classField == fp.getTerminal()) {
                    return fac.conPattern(fp.getUnitT().getRef());
                }
            }

            if (expr instanceof CoreAppExpression) {
                if (((CoreAppExpression) expr).getFunction() instanceof CoreAppExpression) {
                    var func = ((CoreAppExpression) ((CoreAppExpression) expr).getFunction()).getFunction();
                    if (func instanceof CoreFieldCallExpression) {
                        var classField = ((CoreFieldCallExpression) func).getDefinition();
                        var arg1 = ((CoreAppExpression) ((CoreAppExpression) expr).getFunction()).getArgument();
                        var arg2 = ((CoreAppExpression) expr).getArgument();
                        if (classField == fp.getBprod()) {
                            return fac.conPattern(fp.getProd().getRef(), constructPattern(arg1), constructPattern(arg2));
                        }
                    }
                }
            }
            return null;
        }

//        private ConcretePattern constructPatternNew(CoreExpression expr) {
//            if (expr instanceof CoreSigmaExpression) {
//                var link = ((CoreSigmaExpression) expr).getParameters();
//                try {
//                    link.getBinding().getName();
//                } catch (IllegalStateException e) {
//                    return fac.conPattern(fp.getUnitT().getRef());
//                }
//                List<CoreBinding> bindings = new ArrayList<>();
//                while (link.hasNext()) {
//                    bindings.add(link.getBinding());
//                    link = link.getNext();
//                }
//                var res = constructPattern(bindings.get(bindings.size() - 1).getTypeExpr());
//                for (int i = bindings.size() - 2; i >= 0; i--) {
//                    var cur = constructPattern(bindings.get(i).getTypeExpr());
//                    res = fac.conPattern(fp.getProd().getRef(), cur, res);
//                }
//                return res;
//            }
//            if (expr instanceof CoreReferenceExpression) {
//                var type = expr.computeType();
//                if (type instanceof CoreUniverseExpression) {
//                    int num = bm.getObIndexNew(expr);
//                    return fac.conPattern(fp.getTParam().getRef(), fac.numberPattern(num));
//                }
//            }
//            return null;
//        }

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
                    if (bm.getMorIndexNew(dom, cod, fun) != -1)
                        return param(construct(arg), construct(cod), bm.getMorIndexNew(dom, cod, fun));
                    return app(construct(fun), construct(arg));
                }
            }
            if (expr instanceof CoreReferenceExpression) {
                if (vars.getIndex(expr) != -1) {
                    int idx = vars.getIndex(expr);
                    return varFromCtx(idx);
                }
                var type = expr.computeType();
                if (type instanceof CoreUniverseExpression) {
                    return paramT(bm.getObIndex(bm.newToOld(expr)));
                }
            }
            if (expr instanceof CoreTupleExpression) {
                var fields = ((CoreTupleExpression) expr).getFields();
                if (fields.size() == 0) {
                    return unit(construct(expr.computeType()));
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
                ctx.add(construct(param.getTypeExpr()));
                vars.addValue(param.getBinding().makeReference());
                if (firstStep) {
                    firstStep = false;
                    return construct(body);
                }
                var res = construct(body);
                ctx.remove(ctx.size() - 1);
                vars.getValues().remove(ctx.size());
                ;
                return lam(res);
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
            if (expr instanceof CorePiExpression) {
                var dom = ((CorePiExpression) expr).getParameters().getTypeExpr();
                var cod = ((CorePiExpression) expr).getCodomain();
                return arr(construct(dom), construct(cod));
            }
            return null;
        }

        public ConcreteExpression infer(CoreExpression expr) {
            if (expr instanceof CoreFieldCallExpression) {
                var classField = ((CoreFieldCallExpression) expr).getDefinition();
                if (classField == fp.getCatOb()) {
                    return Type();
                }
                if (classField == fp.getApex()) {
                    return infer(((CoreFieldCallExpression) expr).getArgument());
                }
                if (classField == fp.getTerminal()) {
                    return unitT();
                }
            }
            if (expr instanceof CoreAppExpression) {
                var f = ((CoreAppExpression) expr).getFunction();
                if (f instanceof CoreAppExpression) {
                    var func = ((CoreAppExpression) ((CoreAppExpression) expr).getFunction()).getFunction();
                    if (func instanceof CoreFieldCallExpression) {
                        var classField = ((CoreFieldCallExpression) func).getDefinition();
                        var arg1 = ((CoreAppExpression) ((CoreAppExpression) expr).getFunction()).getArgument();
                        var arg2 = ((CoreAppExpression) expr).getArgument();
                        if (classField == fp.getCatHom()) {
                            return Mor(infer(arg1), infer(arg2));
                        }
                        if (classField == fp.getBprod()) {
                            return prodT(infer(arg1), infer(arg2));
                        }
                        if (classField == fp.getTupleMapCat()) {
                            var arg = ((CoreFieldCallExpression) func).getArgument();
                            if (arg instanceof CoreFieldCallExpression) {
                                if (((CoreFieldCallExpression) arg).getDefinition() == fp.getTerminal()) {
                                    return terminalMap(infer(arg1));
                                }
                            }
                            var args = (((CoreCaseExpression) (((CoreLamExpression) arg2).getBody())).getElimBody().getClauses()
                                    .stream().map(CoreElimClause::getExpression).collect(Collectors.toList()));
                            return tupleMap(infer(args.get(0)), infer(args.get(1)));

                        }
                    }
                    if (func instanceof CoreAppExpression) {
                        var A = infer(((CoreAppExpression) (((CoreAppExpression) ((CoreAppExpression) func).getFunction()).getFunction())).getArgument());
                        var B = infer(((CoreAppExpression) ((CoreAppExpression) func).getFunction()).getArgument());
                        var C = infer(((CoreAppExpression) func).getArgument());
                        var arg1 = infer(((CoreAppExpression) ((CoreAppExpression) expr).getFunction()).getArgument());
                        var arg2 = infer(((CoreAppExpression) expr).getArgument());
                        return comp(A, C, B, arg1, arg2);
                    }
                }
                if (f instanceof CoreFieldCallExpression) {
                    var classField = ((CoreFieldCallExpression) f).getDefinition();
                    if (classField == fp.getIdCat()) {
                        return id(infer(((CoreAppExpression) expr).getArgument()));
                    }
                    if (classField == fp.getProj()) {
                        var ind = ((CoreAppExpression) expr).getArgument();
                        assert ind instanceof CoreIntegerExpression;
                        var i = ((CoreIntegerExpression) ind).getBigInteger().intValue();
                        var dom = ((CoreFieldCallExpression) f).getArgument();
                        return i == 0 ? proj1Map(infer(dom)) : proj2Map(infer(dom));
                    }
                }
            }
            var type = expr.computeType();
            if (type instanceof CoreFieldCallExpression) {
                var classField = ((CoreFieldCallExpression) type).getDefinition();
                if (classField == fp.getCatOb()) {
                    return paramT(bm.obsValues.addValue(expr));
                }
            }
            if (type instanceof CoreAppExpression) {
                var f = ((CoreAppExpression) type).getFunction();
                if (f instanceof CoreAppExpression) {
                    var func = ((CoreAppExpression) ((CoreAppExpression) type).getFunction()).getFunction();
                    if (func instanceof CoreFieldCallExpression) {
                        var classField = ((CoreFieldCallExpression) func).getDefinition();
                        var arg1 = ((CoreAppExpression) ((CoreAppExpression) type).getFunction()).getArgument();
                        var arg2 = ((CoreAppExpression) type).getArgument();
                        if (classField == fp.getCatHom()) {
                            return paramM(infer(arg1), infer(arg2), bm.addMor(arg1, arg2, expr));
                        }
                    }
                }
            }
            return null;
        }

        public ConcreteExpression applyLemma(ConcreteExpression m, ConcreteExpression m1, ConcreteExpression p) {
            return fac.app(fac.ref(fp.getLemma().getRef()),
                    fac.arg(fac.hole(), false),
                    fac.arg(fac.ref(obs), false),
                    fac.arg(fac.ref(mors), false),
                    fac.arg(fac.ref(obsMap), false),
                    fac.arg(fac.ref(morsMap), false),
                    fac.arg(m, true),
                    fac.arg(m1, true),
                    fac.arg(p, true)
            );
        }
    }

    private class TypesTranslator {
        Map<Integer, String> names = new HashMap<>();
        Map<String, ConcreteExpression> myContext = new HashMap<>();
        Map<String, ArendRef> refs = new HashMap<>();
        Map<String, CoreExpression> oldRefs = new HashMap<>();
        Values<UncheckedExpression> values;
        FieldsProvider fp;

        public TypesTranslator(FieldsProvider fp) {
            values = new Values<>(typechecker, marker);
            this.fp = fp;
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
                if (classField == fp.getCatOb()) {
                    return fac.universe(null, null);
                }
                if (classField == fp.getApex()) {
                    return infer(((CoreFieldCallExpression) expr).getArgument());
                }
                if (classField == fp.getTerminal()) {
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
                        if (classField == fp.getCatHom()) {
                            return fac.pi(List.of(fac.param(true, infer(arg1))), infer(arg2));
                        }
                        if (classField == fp.getBprod()) {
                            return fac.sigma(fac.param(true, infer(arg1)), fac.param(true, infer(arg2)));
                        }
                        if (classField == fp.getExp()) {
                            return fac.pi(List.of(fac.param(true, infer(arg1))), infer(arg2));
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


    private FieldsProvider inferCategoryType(ContextData contextData) {
        try {
            var expType = contextData.getExpectedType();
            if (expType instanceof CoreFunCallExpression &&
                    ((CoreFunCallExpression) expType).getDefinition() == ext.prelude.getEquality()) {
                var eq = Utils.toEquality(expType, typechecker.getErrorReporter(), contextData.getMarker());
                expType = eq.getDefCallArguments().get(1).computeType();
            }
            var fun0 = ((CoreAppExpression) expType).getFunction();
            var fun1 = ((CoreAppExpression) fun0).getFunction();
            var cat = ((CoreFieldCallExpression) fun1).getArgument().computeType();
            var def = ((CoreClassCallExpression) cat).getDefinition();
            return def == CartesianPrecat ? cfp : ccfp;
        } catch (Exception e) {
            return null;
        }
    }

    @Override
    public TypedExpression invokeMeta(@NotNull ExpressionTypechecker typechecker, @NotNull ContextData contextData) {
        fac = ext.factory.withData(contextData.getMarker());
        this.typechecker = typechecker;
        marker = contextData.getMarker();
        var fp = inferCategoryType(contextData);
        if (fp == null) {
            return null;
        }
        List<? extends ConcreteArgument> args = contextData.getArguments();
        var context = args.subList(1, args.size()).stream()
                .map(x -> typechecker.typecheck(x.getExpression(), null)).collect(Collectors.toList());
        var ttf = new TypeTermFactory(fp);
        if (contextData.getExpectedType() instanceof CoreFunCallExpression &&
                ((CoreFunCallExpression) contextData.getExpectedType()).getDefinition() == ext.prelude.getEquality()) {
            var eq = Utils.toEquality(contextData.getExpectedType(), typechecker.getErrorReporter(), contextData.getMarker());
            var a = eq.getDefCallArguments().get(1).normalize(NormalizationMode.NF);
            var b = eq.getDefCallArguments().get(2).normalize(NormalizationMode.NF);
            var a1 = ttf.infer(a);
            var b1 = ttf.infer(b);
            var p = args.get(0).getExpression();
            var result = ttf.applyLemma(a1, b1, p);
            var withMaps = ttf.addParameterMaps(result, true);
            return typechecker.typecheck(withMaps, contextData.getExpectedType());
        }
        var translator = new TypesTranslator(fp);
        translator.translateContext(context);
        ConcreteExpression expType = null;
        try {
            expType = translator.infer(contextData.getExpectedType());
        } catch (Exception ignored) {
        }
        var params = translator.generateParams();
        CoreExpression finalExp = null;
        if (expType != null) {
            var finalExp0 = typechecker.typecheck(fac.pi(params, expType), null);
            if (finalExp0 != null)
                finalExp = finalExp0.getExpression();
        }
        var lam0 = typechecker.typecheck(args.get(0).getExpression(), finalExp);
        if (lam0 == null) {
            return null;
        }
        try {
            var lam = lam0.getExpression();
            var bindings = params.stream()
                    .flatMap(concreteParameter -> concreteParameter.getRefList().stream()
                            .map(x -> translator.oldRefs.get(x.getRefName()))).collect(Collectors.toList());
            lam = ttf.bm.set(bindings, lam);
            var constructed = ttf.construct(lam);
            var result = ttf.applyI(constructed);
            var withMaps = ttf.addParameterMaps(result, false);
            return typechecker.typecheck(withMaps, contextData.getExpectedType());
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }
}









