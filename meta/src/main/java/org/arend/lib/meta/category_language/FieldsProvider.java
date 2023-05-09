package org.arend.lib.meta.category_language;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.pattern.ConcretePattern;
import org.arend.ext.core.definition.CoreConstructor;
import org.arend.ext.core.definition.CoreDataDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.reference.ArendRef;
import org.arend.lib.StdExtension;

import java.util.List;

public class FieldsProvider {
    public ConcreteFactory fac;
    public StdExtension ext;


    public ArendRef category;
    public ArendRef TP;
    public ArendRef P;
    public ArendRef FP;
    public ArendRef PP;
    public ArendRef TyF;
    public ArendRef TeF;
    public ArendRef FF;
    public ArendRef PF;

    public FieldsProvider() {
    }

    public void init(ConcreteFactory fac, StdExtension ext) {
        this.fac = fac;
        this.ext = ext;
        category = fac.local("CAT");
        TP = fac.local("TP");
        P = fac.local("P");
        FP = fac.local("FP");
        PP = fac.local("PP");
        TyF = fac.local("TyF");
        TeF = fac.local("TeF");
        FF = fac.local("FF");
        PF = fac.local("PF");
    }

    @Dependency(module = "CategoryLanguage.Util", name = "IT")
    private CoreFunctionDefinition IT;
    @Dependency(module = "CategoryLanguage.Util", name = "I")
    private CoreFunctionDefinition I;
    @Dependency(module = "CategoryLanguage.Heyting", name = "IF")
    private CoreFunctionDefinition IF;
    @Dependency(module = "CategoryLanguage.Heyting", name = "IP")
    private CoreFunctionDefinition IP;

    public ConcreteExpression applyIT(ConcreteExpression type) {
        return fac.app(fac.ref(IT.getRef()), fac.arg(fac.ref(TyF), true), fac.arg(type, true));
    }

    public ConcreteExpression applyI(ConcreteExpression term) {
        return fac.app(fac.ref(I.getRef()), fac.arg(fac.ref(TyF), true), fac.arg(fac.ref(TeF), true),
                fac.arg(term, true));
    }

    public ConcreteExpression applyIF(ConcreteExpression form) {
        return fac.app(fac.ref(IF.getRef()), fac.arg(fac.ref(TyF), true), fac.arg(fac.ref(TeF), true),
                fac.arg(fac.ref(FF), true), fac.arg(form, true));
    }

    public ConcreteExpression applyIP(ConcreteExpression proof) {
        return fac.app(fac.ref(IP.getRef()), fac.arg(fac.ref(TyF), true), fac.arg(fac.ref(TeF), true),
                fac.arg(fac.ref(FF), true), fac.arg(fac.ref(PF), true), fac.arg(proof, true));
    }

    @Dependency(module = "CategoryLanguage.Util", name = "Type")
    public CoreDataDefinition Type;
    @Dependency(module = "CategoryLanguage.Util", name = "Type.TParam")
    private CoreConstructor TParam;
    @Dependency(module = "CategoryLanguage.Util", name = "Type.Prod")
    private CoreConstructor Prod;
    @Dependency(module = "CategoryLanguage.Util", name = "Type.Unit")
    private CoreConstructor UnitT;

    public ExpressionAndPattern paramT(int i) {
        return new ExpressionAndPattern(fac.app(fac.ref(TParam.getRef()),
                fac.arg(fac.ref(TP), false), fac.arg(fac.number(i), true)),
                fac.conPattern(TParam.getRef(), fac.numberPattern(i)));
    }

    public ExpressionAndPattern prodT(ExpressionAndPattern a, ExpressionAndPattern b) {
        return new ExpressionAndPattern(fac.app(fac.ref(Prod.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(a.expr, true),
                fac.arg(b.expr, true)),
                fac.conPattern(Prod.getRef(), a.pattern, b.pattern));
    }

    public ExpressionAndPattern unitT() {
        return new ExpressionAndPattern(fac.app(fac.ref(UnitT.getRef()),
                fac.arg(fac.ref(TP), false)),
                fac.conPattern(UnitT.getRef()));
    }


    @Dependency(module = "CategoryLanguage.Util", name = "Term")
    private CoreDataDefinition Term;
    @Dependency(module = "CategoryLanguage.Util", name = "Term.Tuple")
    private CoreConstructor Tuple;
    @Dependency(module = "CategoryLanguage.Util", name = "Term.unit")
    private CoreConstructor unit;
    @Dependency(module = "CategoryLanguage.Util", name = "Term.Proj1")
    private CoreConstructor Proj1;
    @Dependency(module = "CategoryLanguage.Util", name = "Term.Proj2")
    private CoreConstructor Proj2;
    @Dependency(module = "CategoryLanguage.Util", name = "Term.Param")
    private CoreConstructor Param;
    @Dependency(module = "CategoryLanguage.Util", name = "Term.Var")
    private CoreConstructor Var;


    public ExpressionAndPattern tuple(ExpressionAndPattern a, ExpressionAndPattern b,
                                      ExpressionAndPattern A, ExpressionAndPattern B, List<ArendRef> pathsRefs) {
        var pref = fac.local("p" + pathsRefs.size());
        pathsRefs.add(pref);
        return new ExpressionAndPattern(fac.app(fac.ref(Tuple.getRef()),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                fac.arg(a.expr, true), fac.arg(b.expr, true)),

                fac.conPattern(Tuple.getRef(), A.pattern.implicit(), B.pattern.implicit(), fac.refPattern(pref, null),
                        a.pattern, b.pattern));

    }

    public ExpressionAndPattern unit(ExpressionAndPattern ctx, List<ArendRef> pathsRefs) {
        var pref = fac.local("p" + pathsRefs.size());
        pathsRefs.add(pref);
        return new ExpressionAndPattern(fac.app(fac.ref(unit.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(ctx.expr, false),
                fac.arg(fac.hole(), false),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true)),

                fac.conPattern(unit.getRef(), fac.refPattern(pref, null)));
    }

    public ExpressionAndPattern proj1(ExpressionAndPattern S, ExpressionAndPattern t, List<ArendRef> pathsRefs) {
        return new ExpressionAndPattern(fac.app(fac.ref(Proj1.getRef()),
                fac.arg(t.expr, true)),

                fac.conPattern(Proj1.getRef(), S.pattern.implicit(), t.pattern));
    }

    public ExpressionAndPattern proj2(ExpressionAndPattern S, ExpressionAndPattern t, List<ArendRef> pathsRefs) {
        return new ExpressionAndPattern(fac.app(fac.ref(Proj2.getRef()),
                fac.arg(t.expr, true)),

                fac.conPattern(Proj2.getRef(), S.pattern.implicit(), t.pattern));
    }

    public ExpressionAndPattern param(ExpressionAndPattern t, ExpressionAndPattern T, ExpressionAndPattern d, int i, List<ArendRef> pathsRefs) {
        return new ExpressionAndPattern(fac.app(fac.ref(Param.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(fac.hole(), false),
                fac.arg(T.expr, false),
                fac.arg(fac.number(i), true),
                fac.arg(t.expr, true)),

                fac.conPattern(Param.getRef(), d.pattern.implicit(), fac.numberPattern(i), t.pattern));
    }

    public ExpressionAndPattern var(ExpressionAndPattern T, List<ArendRef> pathsRefs) {
        var pref = fac.local("p" + pathsRefs.size());
        pathsRefs.add(pref);
        return new ExpressionAndPattern(fac.app(fac.ref(Var.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(T.expr, false),
                fac.arg(T.expr, false),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true)),

                fac.conPattern(Var.getRef(), fac.refPattern(pref, null)));
    }

    @Dependency(module = "CategoryLanguage.Util", name = "subst")
    private CoreFunctionDefinition subst;

    public ConcreteExpression subst(ConcreteExpression t1, ConcreteExpression t2) {
        return fac.app(fac.ref(subst.getRef()), fac.arg(t1, true), fac.arg(t2, true));
    }


    @Dependency(module = "CategoryLanguage.Heyting", name = "Formula")
    public CoreDataDefinition Formula;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Formula.Conj")
    private CoreConstructor Conj;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Formula.Eq")
    private CoreConstructor Eq;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Formula.FParam")
    private CoreConstructor FParam;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Formula.FTrue")
    private CoreConstructor FTrue;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Formula.FExists")
    private CoreConstructor FExists;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Formula.FFalse")
    private CoreConstructor FFalse;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Formula.Disj")
    private CoreConstructor Disj;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Formula.Impl")
    private CoreConstructor Impl;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Formula.Forall")
    private CoreConstructor Forall;

    public ExpressionAndPattern conj(ExpressionAndPattern a, ExpressionAndPattern b) {
        return new ExpressionAndPattern(fac.app(fac.ref(Conj.getRef()),
                fac.arg(a.expr, true), fac.arg(b.expr, true)),

                fac.conPattern(Conj.getRef(), a.pattern, b.pattern));
    }

    public ExpressionAndPattern Eq(ExpressionAndPattern a, ExpressionAndPattern b, ExpressionAndPattern T) {
        return new ExpressionAndPattern(fac.app(fac.ref(Eq.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(fac.ref(FP), false),
                fac.arg(a.expr, true), fac.arg(b.expr, true)),

                fac.conPattern(Eq.getRef(), T.pattern.implicit(), a.pattern, b.pattern));
    }

    public ExpressionAndPattern fparam(int n, ExpressionAndPattern t, ExpressionAndPattern dom1) {
        return new ExpressionAndPattern(fac.app(fac.ref(FParam.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(fac.ref(FP), false),
                fac.arg(fac.number(n), true), fac.arg(t.expr, true)),

                fac.conPattern(FParam.getRef(), dom1.pattern.implicit(), fac.numberPattern(n), t.pattern));
    }

    public ExpressionAndPattern ftrue(ExpressionAndPattern dom) {
        return new ExpressionAndPattern(fac.app(fac.ref(FTrue.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(fac.ref(FP), false),
                fac.arg(dom.expr, false)),

                fac.conPattern(FTrue.getRef()));
    }



    public ExpressionAndPattern ffalse(ExpressionAndPattern dom) {
        return new ExpressionAndPattern(fac.app(fac.ref(FFalse.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(fac.ref(FP), false),
                fac.arg(dom.expr, false)),

                fac.conPattern(FFalse.getRef()));
    }

    public ExpressionAndPattern disj(ExpressionAndPattern a, ExpressionAndPattern b) {
        return new ExpressionAndPattern(fac.app(fac.ref(Disj.getRef()),
                fac.arg(a.expr, true), fac.arg(b.expr, true)),

                fac.conPattern(Disj.getRef(), a.pattern, b.pattern));
    }

    public ExpressionAndPattern impl(ExpressionAndPattern a, ExpressionAndPattern b) {
        return new ExpressionAndPattern(fac.app(fac.ref(Impl.getRef()),
                fac.arg(a.expr, true), fac.arg(b.expr, true)),

                fac.conPattern(Impl.getRef(), a.pattern, b.pattern));
    }

    public ExpressionAndPattern exists(ExpressionAndPattern dom1, ExpressionAndPattern form) {
        return new ExpressionAndPattern(fac.app(fac.ref(FExists.getRef()),
                fac.arg(dom1.expr, false), fac.arg(form.expr, true)),

                fac.conPattern(FExists.getRef(), dom1.pattern.implicit(), form.pattern));
    }

    public ExpressionAndPattern forall(ExpressionAndPattern dom1, ExpressionAndPattern form) {
        return new ExpressionAndPattern(fac.app(fac.ref(Forall.getRef()),
                fac.arg(dom1.expr, false), fac.arg(form.expr, true)),

                fac.conPattern(Forall.getRef(), dom1.pattern.implicit(), form.pattern));
    }

    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof")
    public CoreDataDefinition Proof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.idProof")
    private CoreConstructor idProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.transProof")
    private CoreConstructor transProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.substProof")
    private CoreConstructor substProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.reflProof")
    public CoreConstructor reflProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.transportProof")
    public CoreConstructor transportProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.concatProof")
    private CoreConstructor concatProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.pmapProof")
    private CoreConstructor pmapProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.invProof")
    private CoreConstructor invProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.proj1Proof")
    private CoreConstructor proj1Proof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.proj2Proof")
    private CoreConstructor proj2Proof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.tupleProof")
    private CoreConstructor tupleProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.trueProof")
    private CoreConstructor trueProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "proofParam")
    private CoreFunctionDefinition paramProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "recExistsProof")
    private CoreFunctionDefinition recExistsProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "existsConsProof")
    private CoreFunctionDefinition existsConsProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "recDisjProof")
    private CoreFunctionDefinition recDisjProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "inlProof")
    private CoreFunctionDefinition inlProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "inrProof")
    private CoreFunctionDefinition inrProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "abstractionProof2")
    private CoreFunctionDefinition abstractionProof2;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.forallProof2")
    private CoreConstructor forallProof2;
    @Dependency(module = "CategoryLanguage.Heyting", name = "applForallProof")
    private CoreFunctionDefinition applForallProof;
    @Dependency(module = "CategoryLanguage.Heyting", name = "Proof.applicationProof")
    private CoreConstructor applicationProof;


    ConcreteExpression idProof(ConcreteExpression dom, ConcreteExpression form) {
        return fac.app(fac.ref(idProof.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(dom, false),
                fac.arg(fac.ref(FP), false),
                fac.arg(fac.ref(PP), false),
                fac.arg(form, false),
                fac.arg(form, false),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true));
    }

    ConcreteExpression transProof(ConcreteExpression p1, ConcreteExpression p2) {
        return fac.app(fac.ref(transProof.getRef()),
                fac.arg(p1, true),
                fac.arg(p2, true));
    }

    ConcreteExpression substProof(ConcreteExpression term, ConcreteExpression proof) {
        return fac.app(fac.ref(substProof.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(fac.hole(), false),
                fac.arg(fac.ref(FP), false),
                fac.arg(fac.ref(PP), false),
                fac.arg(fac.hole(), false),
                fac.arg(fac.hole(), false),
                fac.arg(fac.hole(), false),
                fac.arg(term, false),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                fac.arg(proof, true));
    }

    ConcreteExpression reflProof(ConcreteExpression a, ConcreteExpression hyp) {
        return fac.app(fac.ref(reflProof.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(fac.hole(), false),
                fac.arg(fac.ref(FP), false),
                fac.arg(fac.ref(PP), false),
                fac.arg(hyp, false),
                fac.arg(fac.hole(), false),
                fac.arg(fac.hole(), false),
                fac.arg(a, false),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true));
    }

    ConcreteExpression transportProof(ConcreteExpression hyp, ConcreteExpression dom1, ConcreteExpression a, ConcreteExpression a1,
                                      ConcreteExpression f1, ConcreteExpression eqProof, ConcreteExpression proof) {
        return fac.app(fac.ref(transportProof.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(fac.hole(), false),
                fac.arg(fac.ref(FP), false),
                fac.arg(fac.ref(PP), false),
                fac.arg(hyp, false),
                fac.arg(fac.hole(), false),
                fac.arg(dom1, false),
                fac.arg(a, false),
                fac.arg(a1, false),
                fac.arg(f1, false),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                fac.arg(eqProof, true),
                fac.arg(proof, true));
    }

    ConcreteExpression concatProof(ConcreteExpression a, ConcreteExpression b, ConcreteExpression c, ConcreteExpression proof1, ConcreteExpression proof2) {
        return fac.app(fac.ref(concatProof.getRef()),
                fac.arg(a, true),
                fac.arg(b, true),
                fac.arg(c, true),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                fac.arg(proof1, true),
                fac.arg(proof2, true));
    }

    ConcreteExpression pmapProof(ConcreteExpression a, ConcreteExpression b, ConcreteExpression h, ConcreteExpression proof) {
        return fac.app(fac.ref(pmapProof.getRef()),
//                fac.arg(a, false),
//                fac.arg(b, false),
                fac.arg(h, true),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                fac.arg(proof, true));
    }

    ConcreteExpression invProof(ConcreteExpression a, ConcreteExpression b, ConcreteExpression proof) {
        return fac.app(fac.ref(invProof.getRef()),
//                fac.arg(a, false),
//                fac.arg(b, false),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                fac.arg(proof, true));
    }

    ConcreteExpression proj1Proof(ConcreteExpression form, ConcreteExpression f2) {
        return fac.app(fac.ref(proj1Proof.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(fac.hole(), false),
                fac.arg(fac.ref(FP), false),
                fac.arg(fac.ref(PP), false),
                fac.arg(fac.hole(), false),
                fac.arg(form, false),
                fac.arg(f2, false),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true));
    }

    ConcreteExpression proj2Proof(ConcreteExpression form, ConcreteExpression f1) {
        return fac.app(fac.ref(proj2Proof.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(fac.hole(), false),
                fac.arg(fac.ref(FP), false),
                fac.arg(fac.ref(PP), false),
                fac.arg(fac.hole(), false),
                fac.arg(form, false),
                fac.arg(f1, false),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true));
    }

    ConcreteExpression tupleProof(ConcreteExpression f1, ConcreteExpression f2, ConcreteExpression proof1, ConcreteExpression proof2) {
        return fac.app(fac.ref(tupleProof.getRef()),
//                fac.arg(f1, false),
//                fac.arg(f2, false),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                fac.arg(proof1, true),
                fac.arg(proof2, true));
    }

    ConcreteExpression paramProof(ConcreteExpression hyp, ConcreteExpression form, ConcreteExpression term, ConcreteExpression proofHyp, int n) {
        return fac.app(fac.ref(paramProof.getRef()),
                fac.arg(hyp, true),
                fac.arg(form, true),
                fac.arg(fac.number(n), true),
                fac.arg(term, true),
                fac.arg(proofHyp, true));
    }

    ConcreteExpression trueProof(ConcreteExpression dom, ConcreteExpression hyp) {
        return fac.app(fac.ref(trueProof.getRef()),
                fac.arg(fac.ref(TP), false),
                fac.arg(fac.ref(P), false),
                fac.arg(dom, false),
                fac.arg(fac.ref(FP), false),
                fac.arg(fac.ref(PP), false),
                fac.arg(hyp, false),
                fac.arg(fac.hole(), false),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true));
    }

    ConcreteExpression recExistsProof(ConcreteExpression existsProof, ConcreteExpression proof) {
        return fac.app(fac.ref(recExistsProof.getRef()),
                fac.arg(existsProof, true),
                fac.arg(proof, true));
    }

    ConcreteExpression existsConsProof(ConcreteExpression term, ConcreteExpression proof) {
        return fac.app(fac.ref(existsConsProof.getRef()),
                fac.arg(term, true),
                fac.arg(proof, true));
    }

    ConcreteExpression recDisjProof(ConcreteExpression disjProof, ConcreteExpression p1, ConcreteExpression p2) {
        return fac.app(fac.ref(recDisjProof.getRef()),
                fac.arg(disjProof, true),
                fac.arg(p1, true),
                fac.arg(p2, true));
    }

    ConcreteExpression inlProof(ConcreteExpression proof) {
        return fac.app(fac.ref(inlProof.getRef()),
                fac.arg(proof, true));
    }

    ConcreteExpression inrProof(ConcreteExpression proof) {
        return fac.app(fac.ref(inrProof.getRef()),
                fac.arg(proof, true));
    }

    ConcreteExpression abstrImplProof(ConcreteExpression proof) {
        return fac.app(fac.ref(abstractionProof2.getRef()),
                fac.arg(proof, true));
    }

    ConcreteExpression abstrForallProof(ConcreteExpression proof) {
        return fac.app(fac.ref(forallProof2.getRef()),
                fac.arg(fac.ref(ext.prelude.getIdp().getRef()), true),
                fac.arg(proof, true));
    }

    ConcreteExpression appImplProof(ConcreteExpression hypProof, ConcreteExpression implProof) {
        return fac.app(fac.ref(applicationProof.getRef()),
                fac.arg(hypProof, true),
                fac.arg(implProof, true));
    }

    ConcreteExpression appForallProof(ConcreteExpression forallProof, ConcreteExpression term) {
        return fac.app(fac.ref(applicationProof.getRef()),
                fac.arg(forallProof, true),
                fac.arg(term, true));
    }


    public static class ExpressionAndPattern {
        ConcreteExpression expr;
        ConcretePattern pattern;

        public ExpressionAndPattern(ConcreteExpression expr, ConcretePattern pattern) {
            this.expr = expr;
            this.pattern = pattern;
        }
    }
}

