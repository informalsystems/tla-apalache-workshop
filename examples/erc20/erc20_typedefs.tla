-------------------------- MODULE erc20_typedefs -------------------------------
EXTENDS Variants

(*
  Type definitions for erc20.

  ADDR is an uninterpreted type representing the account address.

  An EVM integer is 256 bits.
  We are using TLA+ integers and check for overflows manually.

  // A state of an ERC20 contract/token
  @typeAlias: state = {
    balanceOf: ADDR -> Int,
    totalSupply: Int,
    allowance: <<ADDR, ADDR>> -> Int,
    owner: ADDR
  };

  // A state of an ERC20 contract/token
  @typeAlias: result =
      Error(Str)
    | Ok({ returnedTrue: Bool, state: $state })
  ;
 *)

erc20_typedefs == TRUE

\* A convinience operator for constructing an Error result.
\*
\* @type: Str => $result;
Error(msg) ==
    Variant("Error", msg)

\* A convinience operator for constructing an Ok result.
\*
\* @type: (Bool, $state) => $result;
Ok(returnedTrue, state) ==
    Variant("Ok", [ returnedTrue |-> returnedTrue, state |-> state ])

================================================================================