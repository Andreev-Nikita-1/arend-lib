package org.arend.lib.meta.category_language;

import org.arend.ext.concrete.ConcreteFactory;
import org.arend.ext.concrete.ConcreteParameter;
import org.arend.ext.concrete.ConcreteSourceNode;
import org.arend.ext.concrete.expr.ConcreteArgument;
import org.arend.ext.core.context.CoreBinding;
import org.arend.ext.core.context.CoreParameter;
import org.arend.ext.core.definition.CoreDataDefinition;
import org.arend.ext.core.definition.CoreFunctionDefinition;
import org.arend.ext.core.expr.*;
import org.arend.ext.core.ops.NormalizationMode;
import org.arend.ext.dependency.Dependency;
import org.arend.ext.error.ErrorReporter;
import org.arend.ext.error.TypecheckingError;
import org.arend.ext.reference.ArendRef;
import org.arend.ext.typechecking.ExpressionTypechecker;
import org.arend.lib.StdExtension;
import org.arend.lib.meta.util.SubstitutionMeta;
import org.arend.lib.util.Values;

import java.util.*;
import java.util.stream.Collectors;

public class Canonizer {
    ConcreteFactory fac;
    StdExtension ext;
    ExpressionTypechecker typechecker;
    ConcreteSourceNode marker;
    ErrorReporter errorReporter;

    Values<CoreReferenceExpression> oldRefs;
    List<ArendRef> newRefs = new ArrayList<>();

    public void init(ConcreteFactory fac, StdExtension ext, ExpressionTypechecker typechecker, ConcreteSourceNode marker) {
        this.fac = fac;
        this.ext = ext;
        this.typechecker = typechecker;
        this.marker = marker;
        errorReporter = typechecker.getErrorReporter();
        this.oldRefs = new Values<>(typechecker, marker);
        ev_unit_lam = (CoreLamExpression) ev_unit.getActualBody();
        ev_true_lam = (CoreLamExpression) ev_true.getActualBody();
        carry2_lam = (CoreLamExpression) carry2.getActualBody();
        carry3_lam = (CoreLamExpression) carry3.getActualBody();
        carry4_lam = (CoreLamExpression) carry4.getActualBody();
        carry5_lam = (CoreLamExpression) carry5.getActualBody();
        carry6_lam = (CoreLamExpression) carry6.getActualBody();
    }

    @Dependency(module = "CategoryLanguage.Util", name = "ev-unit")
    private CoreFunctionDefinition ev_unit;
    @Dependency(module = "CategoryLanguage.Util", name = "ev-true")
    private CoreFunctionDefinition ev_true;
    @Dependency(module = "CategoryLanguage.Util", name = "True")
    private CoreDataDefinition True;
    @Dependency(module = "CategoryLanguage.Util", name = "carry2")
    private CoreFunctionDefinition carry2;
    @Dependency(module = "CategoryLanguage.Util", name = "carry3")
    private CoreFunctionDefinition carry3;
    @Dependency(module = "CategoryLanguage.Util", name = "carry4")
    private CoreFunctionDefinition carry4;
    @Dependency(module = "CategoryLanguage.Util", name = "carry5")
    private CoreFunctionDefinition carry5;
    @Dependency(module = "CategoryLanguage.Util", name = "carry6")
    private CoreFunctionDefinition carry6;

    private CoreLamExpression ev_unit_lam;
    private CoreLamExpression ev_true_lam;
    private CoreLamExpression carry2_lam;
    private CoreLamExpression carry3_lam;
    private CoreLamExpression carry4_lam;
    private CoreLamExpression carry5_lam;
    private CoreLamExpression carry6_lam;


    private static class HandledParameter {
        ConcreteParameter param;
        ConcreteArgument arg;

        public HandledParameter(ConcreteParameter param, ConcreteArgument arg) {
            this.param = param;
            this.arg = arg;
        }
    }

    private boolean isType(CoreExpression type) {
        if (type instanceof CoreUniverseExpression typeUniverse) {
            return Objects.requireNonNull(typeUniverse.getSort().getHLevel()).getConstant() == 0;
        }
        return false;
    }

    private boolean isTerm(CoreExpression type) {
        if (type instanceof CoreReferenceExpression && type.computeType() instanceof CoreUniverseExpression universeExpression) {
            return Objects.requireNonNull(universeExpression.getSort().getHLevel()).getConstant() == 0;
        }
        if (type instanceof CorePiExpression typePi) {
            var cod = typePi.getCodomain();
            return isTerm(cod);
        }
        return false;
    }

    private boolean isPred(CoreExpression type) {
        if (type instanceof CorePiExpression typePi) {
            var cod = typePi.getCodomain();
            if (cod instanceof CoreUniverseExpression codUniverse) {
                return Objects.requireNonNull(codUniverse.getSort().getHLevel()).getConstant() == -1;
            } else {
                return isPred(cod);
            }
        } else if (type instanceof CoreUniverseExpression typeUniverse) {
            return Objects.requireNonNull(typeUniverse.getSort().getHLevel()).getConstant() == -1;
        }
        return false;
    }

    private HandledParameter handleDontModify(CoreParameter parameter) {
        var ref = fac.local(parameter.getBinding().getName());

        var substLam = SubstitutionMeta.makeLambda(parameter.getTypeExpr(),
                oldRefs.getValues().stream().map(CoreReferenceExpression::getBinding).collect(Collectors.toList()), fac, null);
        var formB = fac.appBuilder(substLam);
        for (var x : newRefs) {
            formB = formB.app(fac.arg(fac.ref(x), true));
        }
        var form = formB.build();
        var param = fac.param(List.of(ref), form);
        var arg = fac.arg(fac.ref(ref), true);

        if (oldRefs.getIndex(parameter.getBinding().makeReference()) == -1) {
            oldRefs.addValue(parameter.getBinding().makeReference());
            newRefs.add(ref);
        }
        return new HandledParameter(param, arg);
    }

    private HandledParameter handleType(CoreParameter parameter) {
        var ref = fac.local(parameter.getBinding().getName());
        if (oldRefs.getIndex(parameter.getBinding().makeReference()) == -1) {
            oldRefs.addValue(parameter.getBinding().makeReference());
            newRefs.add(ref);
        }
        var param = fac.param(List.of(ref), fac.core(parameter.getTypedType()));
        var arg = fac.arg(fac.ref(ref), true);
        return new HandledParameter(param, arg);
    }

    private HandledParameter handleTerm(CoreParameter parameter) {
        var type = parameter.getTypeExpr();
        var ref = fac.local(parameter.getBinding().getName());
        ConcreteParameter param = null;
        ConcreteArgument arg = null;
        if (type instanceof CoreReferenceExpression) {
            var typeRef = newRefs.get(oldRefs.getIndex(type));
            param = fac.param(List.of(ref),
                    fac.pi(List.of(fac.param(true, List.of(fac.local("_")), fac.sigma())),
                            fac.ref(typeRef)));
            arg = fac.arg(fac.app(fac.core(ev_unit_lam.computeTyped()), fac.arg(fac.ref(ref), true)), true);
        } else if (type instanceof CorePiExpression typePi) {
            var cod = typePi.getCodomain();
            if (cod instanceof CoreReferenceExpression) {
                var codTypeRef = newRefs.get(oldRefs.getIndex(cod));
                var domTypeRef = newRefs.get(oldRefs.getIndex(typePi.getParameters().getTypeExpr()));
                param = fac.param(List.of(ref),
                        fac.pi(List.of(fac.param(true, List.of(fac.local("_")), fac.ref(domTypeRef))),
                                fac.ref(codTypeRef)));
                arg = fac.arg(fac.ref(ref), true);
            } else if (cod instanceof CorePiExpression codPi) {
                List<ConcreteParameter> sigmaParameters = new ArrayList<>();
                var domTypeRef1 = newRefs.get(oldRefs.getIndex(typePi.getParameters().getTypeExpr()));
                sigmaParameters.add(fac.param(List.of(fac.local("_")), fac.ref(domTypeRef1)));
                var domTypeRef2 = newRefs.get(oldRefs.getIndex(codPi.getParameters().getTypeExpr()));
                sigmaParameters.add(fac.param(List.of(fac.local("_")), fac.ref(domTypeRef2)));
                while (codPi.getCodomain() instanceof CorePiExpression codCodPi) {
                    codPi = codCodPi;
                    var domTypeRefn = newRefs.get(oldRefs.getIndex(codPi.getParameters().getTypeExpr()));
                    sigmaParameters.add(fac.param(List.of(fac.local("_")), fac.ref(domTypeRefn)));
                }
                if (codPi.getCodomain() instanceof CoreReferenceExpression codRef) {
                    var codTypeRef = newRefs.get(oldRefs.getIndex(codRef));
                    param = fac.param(List.of(ref), fac.pi(List.of(
                                    fac.param(true, List.of(fac.local("_")), fac.sigma(sigmaParameters))),
                            fac.ref(codTypeRef)));
                    var carrys = List.of(carry2_lam, carry3_lam, carry4_lam, carry5_lam, carry6_lam);
                    if (sigmaParameters.size() - 2 >= carrys.size()) {
                        errorReporter.report(new TypecheckingError("Maximum number of arguments in functional symbol = " + (carrys.size() + 1), marker));
                    }
                    arg = fac.arg(fac.app(fac.core((carrys.get(sigmaParameters.size() - 2).computeTyped())), fac.arg(fac.ref(ref), true)), true);
                }
            }
        }
        assert param != null;
        return new HandledParameter(param, arg);
    }

    private HandledParameter handlePred(CoreParameter parameter) {

        var type = parameter.getTypeExpr();
        var ref = fac.local(parameter.getBinding().getName());
        fac.ref(parameter.getBinding()).getReferent();
        ConcreteParameter param = null;
        ConcreteArgument arg = null;
        if (type instanceof CoreUniverseExpression) {
            param = fac.param(List.of(ref),
                    fac.pi(List.of(fac.param(true, List.of(fac.local("_")), fac.sigma())),
                            (fac.core(type.computeTyped()))));
            arg = fac.arg(fac.app(fac.core(ev_unit_lam.computeTyped()), fac.arg(fac.ref(ref), true)), true);
        } else if (type instanceof CorePiExpression typePi) {
            var cod = typePi.getCodomain();
            if (cod instanceof CoreUniverseExpression) {
                var domTypeRef = newRefs.get(oldRefs.getIndex(typePi.getParameters().getTypeExpr()));
                param = fac.param(List.of(ref),
                        fac.pi(List.of(fac.param(true, List.of(fac.local("_")), fac.ref(domTypeRef))),
                                fac.core(cod.computeTyped())));
                arg = fac.arg(fac.ref(ref), true);
            } else if (cod instanceof CorePiExpression codPi) {
                List<ConcreteParameter> sigmaParameters = new ArrayList<>();
                var domTypeRef1 = newRefs.get(oldRefs.getIndex(typePi.getParameters().getTypeExpr()));
                sigmaParameters.add(fac.param(List.of(fac.local("_")), fac.ref(domTypeRef1)));
                var domTypeRef2 = newRefs.get(oldRefs.getIndex(codPi.getParameters().getTypeExpr()));
                sigmaParameters.add(fac.param(List.of(fac.local("_")), fac.ref(domTypeRef2)));
                while (codPi.getCodomain() instanceof CorePiExpression codCodPi) {
                    codPi = codCodPi;
                    var domTypeRefn = newRefs.get(oldRefs.getIndex(codPi.getParameters().getTypeExpr()));
                    sigmaParameters.add(fac.param(List.of(fac.local("_")), fac.ref(domTypeRefn)));
                }
                if (codPi.getCodomain() instanceof CoreUniverseExpression) {
                    param = fac.param(List.of(ref), fac.pi(List.of(
                                    fac.param(true, List.of(fac.local("_")), fac.sigma(sigmaParameters))),
                            fac.core(codPi.getCodomain().computeTyped())));
                    var carrys = List.of(carry2_lam, carry3_lam, carry4_lam, carry5_lam, carry6_lam);
                    if (sigmaParameters.size() - 2 >= carrys.size()) {
                        errorReporter.report(new TypecheckingError("Maximum number of arguments in predicate symbol = " + (carrys.size() + 1), marker));
                    }
                    arg = fac.arg(fac.app(fac.core((carrys.get(sigmaParameters.size() - 2).computeTyped())), fac.arg(fac.ref(ref), true)), true);
                }
            }
        }

        return new HandledParameter(param, arg);
    }

    public CoreExpression canonizeParameters(CoreExpression expr, int proofStart, boolean handleProofParams) {
        var cur = expr;
        List<ConcreteParameter> parameters = new ArrayList<>();
        List<ConcreteArgument> arguments = new ArrayList<>();
        boolean termsPredsDone = false;
        while (cur instanceof CoreLamExpression lam && proofStart > 0) {
            var param = lam.getParameters();
            while (param.hasNext()) {
                proofStart--;
                HandledParameter handled;
                try {
                    if (isType(param.getTypeExpr())) {
                        handled = handleProofParams ? handleDontModify(param) : handleType(param);
                    } else if (isTerm(param.getTypeExpr())) {
                        handled = handleProofParams ? handleDontModify(param) : handleTerm(param);
                    } else if (isPred(param.getTypeExpr())) {
                        handled = handleProofParams ? handleDontModify(param) : handlePred(param);
                    } else if (handleProofParams) {
                        handled = handleProofParam(param);
                    } else {
                        termsPredsDone = true;
                        break;
                    }
                } catch (Exception e) {
                    errorReporter.report(new TypecheckingError("Error when parsing parameters.\n Parameters should be listed in following order: sets, functional symbols, predicate symbols, proof parameters. All functional types must be curried.", marker));
                    return null;
                }
                parameters.add(handled.param);
                arguments.add(handled.arg);
                param = param.getNext();
            }
            cur = lam.getBody();
            if (termsPredsDone) {
                break;
            }
        }
        assert !handleProofParams || proofStart == 0;

        if (handleProofParams) {
            if (cur instanceof CoreLamExpression curLam) {
                var parType = curLam.getParameters().getTypeExpr();
                if (exprIsType(parType)) {
                    var body = curLam.getBody();
                    if (!(body instanceof CoreLamExpression bodyLam) || exprIsType(bodyLam.getParameters().getTypeExpr())) {
                        // TODO add multiples variables as ctx
                        var ref = fac.local(curLam.getParameters().getBinding().getName());
                        parameters.add(fac.param(List.of(ref), fac.ref(newRefs.get(oldRefs.getIndex(curLam.getParameters().getTypeExpr())))));
                        parameters.add(fac.param(List.of(fac.local("p_of_true_as_sequence_hypothesis")), fac.ref(True.getRef())));
                        arguments.add(fac.arg(fac.ref(ref), true));
                    }
                } else {
                    parameters.add(fac.param(List.of(fac.local("x_of_sigma_domain")), fac.sigma()));
                }
            } else {
                parameters.add(fac.param(List.of(fac.local("x_of_sigma_domain")), fac.sigma()));
                parameters.add(fac.param(List.of(fac.local("p_of_true_as_sequence_hypothesis")), fac.ref(True.getRef())));
            }
        }

        var res = fac.lam(parameters, fac.app(fac.core(expr.computeTyped()), arguments));
        var resCore = typechecker.typecheck(res, null);
        if (resCore == null || resCore.getExpression() instanceof CoreErrorExpression) {
            errorReporter.report(new TypecheckingError("Error when parsing parameters.\n Parameters should be listed in following order: sets, functional symbols, predicate symbols, proof parameters. All functional types must be curried.", marker));
            return null;
        }
        return resCore.getExpression().normalize(NormalizationMode.WHNF);
    }


    private boolean exprIsType(CoreExpression expr) {
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
        return expr instanceof CoreReferenceExpression;
    }


    private HandledParameter handleProofParam(CoreParameter parameter) {
        var type = parameter.getTypeExpr();
        var ref = fac.local(parameter.getBinding().getName());
        ConcreteParameter param;
        ConcreteArgument arg;
        if (type instanceof CorePiExpression typePi) {
            var typeParam = typePi.getParameters().getTypeExpr();
            var cod = typePi.getCodomain();
            if (exprIsType(typeParam)) {
                if (cod instanceof CorePiExpression codPi && !exprIsType(codPi.getParameters().getTypeExpr())) {
                    // TODO add multiple parameters as ctx
                    var xRef = fac.local(typePi.getParameters().getBinding().getName());
                    oldRefs.addValue(typePi.getParameters().getBinding().makeReference());
                    newRefs.add(xRef);
                    var substLam = SubstitutionMeta.makeLambda(typePi.getCodomain(),
                            oldRefs.getValues().stream().map(CoreReferenceExpression::getBinding).collect(Collectors.toList()), fac, null);
                    var formB = fac.appBuilder(substLam);
                    for (var x : newRefs) {
                        formB = formB.app(fac.arg(fac.ref(x), true));
                    }
                    var form = formB.build();
                    oldRefs.getValues().remove(oldRefs.getValues().size() - 1);
                    newRefs.remove(newRefs.size() - 1);
                    param = fac.param(List.of(ref),
                            fac.pi(List.of(fac.param(true, List.of(xRef), fac.ref(newRefs.get(oldRefs.getIndex(typeParam))))),
                                    form));
                    arg = fac.arg(fac.ref(ref), true);

                } else {
                    var xRef = fac.local(typePi.getParameters().getBinding().getName());
                    oldRefs.addValue(typePi.getParameters().getBinding().makeReference());
                    newRefs.add(xRef);
                    var substLam = SubstitutionMeta.makeLambda(typePi.getCodomain(),
                            oldRefs.getValues().stream().map(CoreReferenceExpression::getBinding).collect(Collectors.toList()), fac, null);
                    var formB = fac.appBuilder(substLam);
                    for (var x : newRefs) {
                        formB = formB.app(fac.arg(fac.ref(x), true));
                    }
                    var form = formB.build();
                    oldRefs.getValues().remove(oldRefs.getValues().size() - 1);
                    newRefs.remove(newRefs.size() - 1);
                    param = fac.param(List.of(ref),
                            fac.pi(List.of(fac.param(true, List.of(xRef), fac.ref(newRefs.get(oldRefs.getIndex(typeParam))))),
                                    fac.pi(List.of(fac.param(true, List.of(fac.local("_")), fac.app(fac.ref(True.getRef())))),
                                            form)));
                    arg = fac.arg(fac.app(fac.core(ev_true_lam.computeTyped()),
                            fac.arg(fac.ref(ref), true)), true);
                }
            } else {
                var substLam = SubstitutionMeta.makeLambda(type,
                        oldRefs.getValues().stream().map(CoreReferenceExpression::getBinding).collect(Collectors.toList()), fac, null);
                var formB = fac.appBuilder(substLam);
                for (var x : newRefs) {
                    formB = formB.app(fac.arg(fac.ref(x), true));
                }
                var form = formB.build();
                param = fac.param(List.of(ref),
                        fac.pi(List.of(fac.param(true, List.of(fac.local("_")), fac.sigma())),
                                form));
                arg = fac.arg(fac.app(fac.core(ev_unit_lam.computeTyped()),
                        fac.arg(fac.ref(ref), true)), true);
            }
        } else {
            var substLam = SubstitutionMeta.makeLambda(type,
                    oldRefs.getValues().stream().map(CoreReferenceExpression::getBinding).collect(Collectors.toList()), fac, null);
            var formB = fac.appBuilder(substLam);
            for (var x : newRefs) {
                formB = formB.app(fac.arg(fac.ref(x), true));
            }
            var form = formB.build();
            param = fac.param(List.of(ref),
                    fac.pi(List.of(fac.param(true, List.of(fac.local("_")), fac.sigma()),
                                    fac.param(true, List.of(fac.local("_")), fac.app(fac.ref(True.getRef())))),
                            form));
            arg = fac.arg(fac.app(fac.core(ev_unit_lam.computeTyped()),
                    fac.arg(fac.app(fac.core(ev_true_lam.computeTyped()),
                            fac.arg(fac.ref(ref), true)), true)), true);
        }
        return new HandledParameter(param, arg);
    }


    public CoreExpression canonize(CoreExpression expr, int proofStart) {
        var termsPredsHandled = canonizeParameters(expr, proofStart, false);
        oldRefs = new Values<>(typechecker, marker);
        newRefs = new ArrayList<>();
        if (termsPredsHandled == null) {
            return null;
        }
        return canonizeParameters(termsPredsHandled, proofStart, true);
    }
}