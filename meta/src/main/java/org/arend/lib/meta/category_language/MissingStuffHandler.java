//package org.arend.lib.meta.category_language;
//
//import org.arend.ext.concrete.ConcreteFactory;
//import org.arend.ext.concrete.ConcreteParameter;
//import org.arend.ext.concrete.ConcreteSourceNode;
//import org.arend.ext.concrete.expr.ConcreteExpression;
//import org.arend.ext.core.context.CoreParameter;
//import org.arend.ext.core.definition.CoreFunctionDefinition;
//import org.arend.ext.core.expr.CoreExpression;
//import org.arend.ext.core.expr.CoreLamExpression;
//import org.arend.ext.core.expr.CorePiExpression;
//import org.arend.ext.core.expr.CoreUniverseExpression;
//import org.arend.ext.dependency.Dependency;
//import org.arend.ext.typechecking.ExpressionTypechecker;
//import org.arend.lib.StdExtension;
//
//import java.util.ArrayList;
//import java.util.List;
//
//public class MissingStuffHandler {
//    private static ConcreteFactory fac;
//    ExpressionTypechecker typechecker;
//    ConcreteSourceNode marker;
//    private StdExtension ext;
//
//    @Dependency(module = "CategoryLanguage.Util", name = "subst-unit")
//    private static CoreFunctionDefinition substUnit;
//    @Dependency(module = "CategoryLanguage.Util", name = "carry-function")
//    private static CoreFunctionDefinition carryFunction;
//
//
//    public static ConcreteExpression handleType(CoreParameter parameter, List<ConcreteParameter> paramsAcc, ConcreteExpression application) {
//        var ref = parameter.getBinding();
//        ConcreteExpression argRes = fac.ref(ref);
//        ConcreteParameter paramRes = fac.param(true, fac.ref(ref));
//
//        paramsAcc.add(paramRes);
//        return fac.app(application, fac.arg(argRes, true));
//    }
//
//    public static ConcreteExpression handleTerm(CoreParameter parameter, List<ConcreteParameter> paramsAcc, ConcreteExpression application) {
//        var ref = fac.local(parameter.getBinding().getName());
//        ConcreteExpression argRes;
//        ConcreteParameter paramRes;
//
//        var type = parameter.getTypeExpr();
//        if (type instanceof CorePiExpression typePi) { // functional symbol
//            var codomain = typePi.getCodomain();
//            if (codomain instanceof CorePiExpression codPi) { // with >= two parameters
//                var codomain1 = codPi.getCodomain();
//                if (codomain1 instanceof CorePiExpression) { // >= 3 parameters
//                    return null;
//                }
//                var A = fac.param(true, fac.core(typePi.getParameters().getTypedType()));
//                var B = fac.param(true, fac.core(codPi.getParameters().getTypedType()));
//                paramRes = fac.param(true, List.of(ref),
//                        fac.pi(List.of(fac.param(true, fac.sigma(A, B))), fac.core(codomain1.computeTyped())));
//                argRes = fac.app(fac.ref(carryFunction.getRef()), fac.arg(fac.ref(ref), true));
//            } else { // with one parameter
//                paramRes = fac.param(true, List.of(ref), fac.core(type.computeTyped()));
//                argRes = fac.ref(ref);
//            }
//        } else { // constant symbol
//            paramRes = fac.param(true, List.of(ref), fac.pi(List.of(fac.param(true, fac.sigma())), fac.core(type.computeTyped())));
//            argRes = fac.app(fac.ref(substUnit.getRef()), fac.arg(fac.ref(ref), true));
//        }
//        paramsAcc.add(paramRes);
//        return fac.app(application, fac.arg(argRes, true));
//    }
//
//
//    public static ConcreteExpression handleTerms(CoreExpression lam, int proofStart) {
//
//        ConcreteExpression application = fac.core(lam.computeTyped());
//        List<ConcreteParameter> parameters = new ArrayList<>();
//
//        while (proofStart > 0) {
//            if (lam instanceof CoreLamExpression) {
//                var params = ((CoreLamExpression) lam).getParameters();
//                while (params.hasNext()) {
//                    proofStart--;
//                    var type = params.getTypeExpr();
//                    if (type instanceof CoreUniverseExpression) { // type parameter
//                        application = handleType(params, parameters, application);
//                    } else {
//                        application = handleTerm(params, parameters, application);
//                    }
//                    params = params.getNext();
//                }
//                lam = ((CoreLamExpression) lam).getBody();
//            }
//        }
//        return fac.lam(parameters, application);
//    }
//
//}
