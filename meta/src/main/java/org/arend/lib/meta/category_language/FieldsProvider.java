package org.arend.lib.meta.category_language;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.pattern.ConcretePattern;
import org.arend.ext.core.definition.CoreClassDefinition;
import org.arend.ext.core.definition.CoreDataDefinition;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.reference.ArendRef;
import org.arend.lib.StdExtension;

import java.util.List;

public abstract class FieldsProvider {

    ConcreteFactory fac;
    StdExtension ext;
    ErrorReporter errorReporter;
    ConcreteSourceNode marker;

    public ArendRef category;
    public ArendRef TP;
    public ArendRef P;
    public ArendRef FP;
    public ArendRef PP;
    public ArendRef TyF;
    public ArendRef TeF;
    public ArendRef FF;
    public ArendRef PF;

    abstract public CoreDataDefinition getFormula();

    abstract public CoreDataDefinition getType();

    abstract public CoreClassDefinition getCategoryDef();

    public void init(ConcreteFactory fac, StdExtension ext, ErrorReporter errorReporter, ConcreteSourceNode marker) {
        this.fac = fac;
        this.ext = ext;
        this.errorReporter = errorReporter;
        this.marker = marker;
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

    abstract ConcreteExpression applyIT(ConcreteExpression type);

    abstract ConcreteExpression applyI(ConcreteExpression term);

    abstract ConcreteExpression applyIF(ConcreteExpression form);

    abstract ConcreteExpression applyIP(ConcreteExpression hyp, ConcreteExpression proof);

    abstract ExpressionAndPattern paramT(int i);

    abstract ExpressionAndPattern prodT(ExpressionAndPattern a, ExpressionAndPattern b);

    abstract ExpressionAndPattern unitT();

    abstract ExpressionAndPattern tuple(ExpressionAndPattern a, ExpressionAndPattern b,
                                        ExpressionAndPattern A, ExpressionAndPattern B, List<ArendRef> pathsRefs);

    abstract ExpressionAndPattern unit(ExpressionAndPattern ctx, List<ArendRef> pathsRefs);

    abstract ExpressionAndPattern proj1(ExpressionAndPattern S, ExpressionAndPattern t, List<ArendRef> pathsRefs);

    abstract ExpressionAndPattern proj2(ExpressionAndPattern S, ExpressionAndPattern t, List<ArendRef> pathsRefs);

    abstract ExpressionAndPattern param(ExpressionAndPattern t, ExpressionAndPattern T, ExpressionAndPattern d, int i, List<ArendRef> pathsRefs);

    abstract ExpressionAndPattern var(ExpressionAndPattern T, List<ArendRef> pathsRefs);

    abstract ExpressionAndPattern conj(ExpressionAndPattern a, ExpressionAndPattern b);

    abstract ExpressionAndPattern Eq(ExpressionAndPattern a, ExpressionAndPattern b, ExpressionAndPattern T);

    abstract ExpressionAndPattern fparam(int n, ExpressionAndPattern t, ExpressionAndPattern dom1);

    abstract ExpressionAndPattern ftrue(ExpressionAndPattern dom);

    abstract ExpressionAndPattern ffalse(ExpressionAndPattern dom);


    abstract ExpressionAndPattern disj(ExpressionAndPattern a, ExpressionAndPattern b);

    abstract ExpressionAndPattern impl(ExpressionAndPattern a, ExpressionAndPattern b);

    abstract ExpressionAndPattern exists(ExpressionAndPattern dom1, ExpressionAndPattern form);

    abstract ExpressionAndPattern forall(ExpressionAndPattern dom1, ExpressionAndPattern form);

    abstract ConcreteExpression idProof(ConcreteExpression dom, ConcreteExpression form);

    abstract ConcreteExpression transProof(ConcreteExpression p1, ConcreteExpression p2);

    abstract ConcreteExpression reflProof(ConcreteExpression a, ConcreteExpression hyp);

    abstract ConcreteExpression transportProof(ConcreteExpression hyp, ConcreteExpression dom1, ConcreteExpression a, ConcreteExpression a1,
                                               ConcreteExpression f1, ConcreteExpression eqProof, ConcreteExpression proof);

    abstract ConcreteExpression concatProof(ConcreteExpression a, ConcreteExpression b, ConcreteExpression c, ConcreteExpression proof1, ConcreteExpression proof2);

    abstract ConcreteExpression pmapProof(ConcreteExpression a, ConcreteExpression b, ConcreteExpression h, ConcreteExpression proof);

    abstract ConcreteExpression invProof(ConcreteExpression a, ConcreteExpression b, ConcreteExpression proof);

    abstract ConcreteExpression proj1Proof(ConcreteExpression form, ConcreteExpression f2);

    abstract ConcreteExpression proj2Proof(ConcreteExpression form, ConcreteExpression f1);

    abstract ConcreteExpression tupleProof(ConcreteExpression f1, ConcreteExpression f2, ConcreteExpression proof1, ConcreteExpression proof2);

    abstract ConcreteExpression paramProof(ConcreteExpression hyp, ConcreteExpression form, ConcreteExpression term, ConcreteExpression proofHyp, int n);

    abstract ConcreteExpression trueProof(ConcreteExpression dom, ConcreteExpression hyp);

    abstract ConcreteExpression recExistsProof(ConcreteExpression f, ConcreteExpression f1,
                                               ConcreteExpression existsProof, ConcreteExpression proof);

    abstract ConcreteExpression existsConsProof(ConcreteExpression form, ConcreteExpression term, ConcreteExpression proof);

    abstract ConcreteExpression recDisjProof(ConcreteExpression disjProof, ConcreteExpression p1, ConcreteExpression p2);

    abstract ConcreteExpression inlProof(ConcreteExpression f2, ConcreteExpression proof);

    abstract ConcreteExpression inrProof(ConcreteExpression f1, ConcreteExpression proof);

    abstract ConcreteExpression absurdProof(ConcreteExpression f, ConcreteExpression proof);

    abstract ConcreteExpression abstrImplProof(ConcreteExpression proof);

    abstract ConcreteExpression abstrForallProof(ConcreteExpression proof);

    abstract ConcreteExpression appImplProof(ConcreteExpression hypProof, ConcreteExpression implProof);

    abstract ConcreteExpression appForallProof(ConcreteExpression forallProof, ConcreteExpression term);

    public static class ExpressionAndPattern {
        ConcreteExpression expr;
        ConcretePattern pattern;

        public ExpressionAndPattern(ConcreteExpression expr, ConcretePattern pattern) {
            this.expr = expr;
            this.pattern = pattern;
        }
    }
}
