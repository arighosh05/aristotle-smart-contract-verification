import Lake
open Lake DSL

package «SmartContractVerification» where

@[default_target]
lean_lib «SmartContractVerification» where
  globs := #[.submodules `evm_model, .submodules `properties]
