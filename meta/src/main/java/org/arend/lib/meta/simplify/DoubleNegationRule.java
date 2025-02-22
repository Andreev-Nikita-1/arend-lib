package org.arend.lib.meta.simplify;

import org.arend.ext.concrete.expr.ConcreteExpression;
import org.arend.ext.concrete.expr.ConcreteReferenceExpression;
import org.arend.ext.core.expr.CoreClassCallExpression;
import org.arend.ext.core.expr.CoreExpression;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.ext.typechecking.TypedExpression;
import org.arend.ext.util.Pair;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.equation.binop_matcher.FunctionMatcher;

import java.util.List;

public class DoubleNegationRule extends LocalSimplificationRuleBase {
  private final FunctionMatcher negativeMatcher;

  public DoubleNegationRule(TypedExpression instance, CoreClassCallExpression classCall, StdExtension ext, ConcreteReferenceExpression refExpr, ExpressionTypechecker typechecker) {
    super(instance, classCall, ext, refExpr, typechecker);
    this.negativeMatcher = FunctionMatcher.makeFieldMatcher(classCall, instance, ext.equationMeta.negative, typechecker, factory, refExpr, ext, 1);
  }

  @Override
  protected Pair<CoreExpression, ConcreteExpression> simplifySubexpression(CoreExpression subexpr) {
    List<CoreExpression> args = negativeMatcher.match(subexpr);
    if (args != null) {
      args = negativeMatcher.match(args.get(0));
      if (args != null) {
        var path = factory.appBuilder(factory.ref(ext.equationMeta.negIsInv.getRef()))
          .app(factory.hole(), false)
          .app(factory.core(args.get(0).computeTyped()), false)
          .build();
        return new Pair<>(args.get(0), path);
      }
    }
    return null;
  }
}
