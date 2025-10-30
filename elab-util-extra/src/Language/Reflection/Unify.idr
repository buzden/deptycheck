module Language.Reflection.Unify

import Language.Reflection
import public Language.Reflection.Unify.Interface
import public Language.Reflection.Unify.WithCompiler

-- export %defaulthint
export %defaulthint
DefaultUnifier : Elaboration m => CanUnify m
DefaultUnifier = UnifyWithCompiler
