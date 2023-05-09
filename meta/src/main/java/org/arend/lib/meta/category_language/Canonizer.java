package org.arend.lib.meta.category_language;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.lib.StdExtension;
import org.arend.lib.util.Values;

import java.util.ArrayList;
import java.util.List;

public class Canonizer {
    ConcreteFactory fac;
    StdExtension ext;
    ExpressionTypechecker typechecker;
    ConcreteSourceNode marker;

    public void init(ConcreteFactory fac, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
        this.fac = fac;
        this.ext = ext;
        this.typechecker = typechecker;
        this.marker = marker;
        this.types = new Values<>(typechecker, marker);
    }

    @Dependency(module = "CategoryLanguage.Util", name = "sigma")
    private CoreFunctionDefinition sigma;
    @Dependency(module = "CategoryLanguage.Util", name = "ev-unit")
    private CoreFunctionDefinition ev_unit;
    @Dependency(module = "CategoryLanguage.Util", name = "carry2")
    private CoreFunctionDefinition carry2;

    public CoreExpression canonize(CoreExpression expr, int proofStart) {
        var cur = expr;
        List<ConcreteParameter> parameters = new ArrayList<>();
        List<ConcreteArgument> arguments = new ArrayList<>();
        while (cur instanceof CoreLamExpression lam && proofStart > 0) {
            var param = lam.getParameters();
            while (param.hasNext()) {
                HandledParameter handled = null;
                if (isType(param.getTypeExpr())) {
                    handled = handleType(param);
                } else if (isTerm(param.getTypeExpr())) {
                    handled = handleTerm(param);
                } else if (isPred(param.getTypeExpr())) {
                    handled = handlePred(param);
                } else {
                    break;
                }
                proofStart--;
                parameters.add(handled.param);
                arguments.add(handled.arg);
                param = param.getNext();
            }
            cur = lam.getBody();
        }
        var res = fac.lam(parameters, fac.app(fac.core(expr.computeTyped()), arguments));
        var resCore = typechecker.typecheck(res, null);
        var resCoreNormalized = resCore.getExpression().normalize(NormalizationMode.NF);
        return resCoreNormalized;
    }


    private static class HandledParameter {
        ConcreteParameter param;
        ConcreteArgument arg;

        public HandledParameter(ConcreteParameter param, ConcreteArgument arg) {
            this.param = param;
            this.arg = arg;
        }
    }

    private boolean isType(CoreExpression type) {
        return type instanceof CoreUniverseExpression;
    }

    private boolean isTerm(CoreExpression type) {
        if (type instanceof CoreReferenceExpression) {
            return true;
        }
        if (type instanceof CorePiExpression typePi) {
            var cod = typePi.getCodomain();
            if (cod instanceof CoreReferenceExpression) {
                return true;
            } else {
                return isTerm(cod);
            }
        }
        return false;
    }

    private boolean isPred(CoreExpression type) {
        if (type instanceof CorePiExpression typePi) {
            var cod = typePi.getCodomain();
            if (cod instanceof CoreUniverseExpression) {
                return true;
            } else {
                return isPred(cod);
            }
        }
        return false;
    }

    Values<CoreReferenceExpression> types;
    List<ArendRef> typesNewRefs = new ArrayList<>();

    private HandledParameter handleType(CoreParameter parameter) {
        var ref = fac.local(parameter.getBinding().getName());
        if (types.getIndex(parameter.getBinding().makeReference()) == -1) {
            types.addValue(parameter.getBinding().makeReference());
            typesNewRefs.add(ref);
        }
        var param = fac.param(List.of(ref), fac.core(parameter.getTypedType()));
        var arg = fac.arg(fac.ref(ref), true);
        return new HandledParameter(param, arg);
    }

    private HandledParameter handleTerm(CoreParameter parameter) {
        var type = parameter.getTypeExpr();
        if (type instanceof CoreReferenceExpression) {
            var ref = fac.local(parameter.getBinding().getName());
            var typeRef = typesNewRefs.get(types.getIndex(type));
            var param = fac.param(List.of(ref),
                    fac.pi(List.of(fac.param(true, List.of(fac.local("")), fac.sigma())),
                            fac.ref(typeRef)));
            var arg = fac.arg(fac.app(fac.ref(ev_unit.getRef()), fac.arg(fac.ref(ref), true)), true);
            return new HandledParameter(param, arg);
        }
        if (type instanceof CorePiExpression typePi) {
            var cod = typePi.getCodomain();
            if (cod instanceof CoreReferenceExpression) {
                var ref = fac.local(parameter.getBinding().getName());
                var codTypeRef = typesNewRefs.get(types.getIndex(cod));
                var domTypeRef = typesNewRefs.get(types.getIndex(typePi.getParameters().getTypeExpr()));
                var param = fac.param(List.of(ref),
                        fac.pi(List.of(fac.param(true, List.of(fac.local("")), fac.ref(domTypeRef))),
                                fac.ref(codTypeRef)));
                var arg = fac.arg(fac.ref(ref), true);
                return new HandledParameter(param, arg);
            } else if (cod instanceof CorePiExpression codPi) {
                var codCod = codPi.getCodomain();
                if (codCod instanceof CoreReferenceExpression) {
                    var ref = fac.local(parameter.getBinding().getName());
                    var codTypeRef = typesNewRefs.get(types.getIndex(codCod));
                    var domTypeRef1 = typesNewRefs.get(types.getIndex(typePi.getParameters().getTypeExpr()));
                    var domTypeRef2 = typesNewRefs.get(types.getIndex(codPi.getParameters().getTypeExpr()));
                    var sigm = fac.sigma(List.of(fac.param(List.of(fac.local("")), fac.ref(domTypeRef1)),
                            fac.param(List.of(fac.local("")), fac.ref(domTypeRef2))));
                    var param = fac.param(List.of(ref),
                            fac.pi(List.of(fac.param(true, List.of(fac.local("")),
                                            sigm)),
                                    fac.ref(codTypeRef)));
                    var arg = fac.arg(fac.app(fac.ref(carry2.getRef()), fac.arg(fac.ref(ref), true)), true);
                    return new HandledParameter(param, arg);
                } else {
                    // carry > 2
                    return null;
                }
            }
        }
        return null;
    }

    private HandledParameter handlePred(CoreParameter parameter) {
        var type = parameter.getTypeExpr();
        if (type instanceof CorePiExpression typePi) {
            var cod = typePi.getCodomain();
            if (cod instanceof CoreUniverseExpression) {
                var ref = fac.local(parameter.getBinding().getName());
                var domTypeRef = typesNewRefs.get(types.getIndex(typePi.getParameters().getTypeExpr()));
                var param = fac.param(List.of(ref),
                        fac.pi(List.of(fac.param(true, List.of(fac.local("")), fac.ref(domTypeRef))),
                                fac.core(cod.computeTyped())));
                var arg = fac.arg(fac.ref(ref), true);
                return new HandledParameter(param, arg);
            } else if (cod instanceof CorePiExpression codPi) {
                var codCod = codPi.getCodomain();
                if (codCod instanceof CoreUniverseExpression) {
                    var ref = fac.local(parameter.getBinding().getName());
                    var domTypeRef1 = typesNewRefs.get(types.getIndex(typePi.getParameters().getTypeExpr()));
                    var domTypeRef2 = typesNewRefs.get(types.getIndex(codPi.getParameters().getTypeExpr()));
                    var sigm = fac.sigma(List.of(fac.param(List.of(fac.local("")), fac.ref(domTypeRef1)),
                            fac.param(List.of(fac.local("")), fac.ref(domTypeRef2))));
                    var param = fac.param(List.of(ref),
                            fac.pi(List.of(fac.param(true, List.of(fac.local("")),
                                            sigm)),
                                    fac.core(codCod.computeTyped())));
                    var arg = fac.arg(fac.app(fac.ref(carry2.getRef()), fac.arg(fac.ref(ref), true)), true);
                    return new HandledParameter(param, arg);
                } else {
                    // carry > 2
                    return null;
                }
            }
        }
        return null;
    }
}
