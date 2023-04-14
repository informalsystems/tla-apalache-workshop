---------------------------- MODULE erc20 -------------------------------------
(*
 * A specification of simple ERC20 that should be easy to use in other specs.
 *
 * The module erc20 closely follows the interface of IERC20 by OpenZeppelin.
 * However, since Quint is not Solidity, we have to adapt to the features of Quint.
 *
 * https://docs.openzeppelin.com/contracts/4.x/api/token/erc20#IERC20
 *
 * Our approach to the TLA+ specification may look non-standard at first.
 * We have first specified this module in Quint and then translated it to TLA+ (by hand).
 *
 * https://github.com/informalsystems/quint/blob/main/examples/solidity/ERC20/erc20.qnt
 *
 * Igor Konnov, Informal Systems, 2023
 *)

EXTENDS Integers, Apalache, erc20_typedefs

CONSTANT
  \* The set of all addresses that we are using
  \*
  \* @type: Set(ADDR);
  AllAddresses

\* The special address, which corresponds to the special address 0x0 in EVM
ZERO_ADDRESS == "0_OF_ADDR"

ASSUME(ZERO_ADDRESS \in AllAddresses)

\* The maximal value of the unsigned integer in EVM
MAX_UINT == 2^256 - 1
\* The predicate that we use to check for overflows
isUint(i) == 0 <= i /\ i <= MAX_UINT

\* Construct a new ERC20 contract
\*
\* @type: (ADDR, Int) => $state;
newErc20(sender, initialSupply) == [
  balanceOf |->
    [ a \in AllAddresses |-> IF a /= sender THEN 0 ELSE initialSupply ],
  totalSupply |-> initialSupply,
  allowance |-> [ a, b \in AllAddresses |-> 0],
  owner |-> sender
]

\* Returns the amount of tokens in existence
\* @type: $state => Int;
totalSupply(state) == state.totalSupply

\* Returns the amount of tokens owned by account
\* @type: ($state, ADDR) => Int;
balanceOf(state, account) == state.balanceOf[account]

\* An internal implementation, similar to OpenZeppelin's
\* https://github.com/OpenZeppelin/openzeppelin-contracts/blob/ca822213f2275a14c26167bd387ac3522da67fe9/contracts/token/ERC20/ERC20.sol#L222
\*
\* @type: ($state, ADDR, ADDR, Int) => $result;
_transfer(state, fromAddr, toAddr, amount) ==
  LET fromBalance == state.balanceOf[fromAddr] IN
  \* check the require(...) statements
  LET err ==
    CASE ~(fromAddr /= ZERO_ADDRESS) -> "ERC20: transfer from the zero address"
      [] ~(toAddr /= ZERO_ADDRESS) -> "ERC20: transfer to the zero address"
      [] ~(fromBalance >= amount) -> "ERC20: transfer amount exceeds balance"
      [] OTHER -> ""
  IN
  IF err /= ""
  THEN Error(err)
  ELSE
    LET newBalances ==
      IF (fromAddr = toAddr)
      THEN state.balanceOf
      ELSE 
        \* Comment from ERC20.sol (see the above link): 
        \* Overflow not possible: the sum of all balances is capped
        \* by totalSupply, and the sum is preserved by
        \* decrementing then incrementing.
        [
          state.balanceOf EXCEPT ![fromAddr] = fromBalance - amount,
                                 ![toAddr] = @ + amount
        ]
    IN
    Ok(TRUE, [ state EXCEPT !.balanceOf = newBalances ])
    
  (*
   * ERC20: Moves amount tokens from the sender’s account to `toAddress`.
   * Returns a boolean value indicating whether the operation succeeded.
   *
   * @type: ($state, ADDR, ADDR, Int) => $result;
   *)
  transfer(state, sender, toAddr, amount) ==
    \* `transfer` always returns true, but we should check Erc20Result.error
    _transfer(state, sender, toAddr, amount)

  (*
   * ERC20: Returns the remaining number of tokens that spender will be allowed to
   * spend on behalf of owner through transferFrom. This is zero by default in EVM.
   *
   * This value may change when approve or transferFrom are called.
   *
   * TLA+: the actual allowance is set up to 0 in newErc20.
   *
   * @type: ($state, ADDR, ADDR) => Int;
   *)
  allowance(state, owner, spender) ==
    state.allowance[owner, spender]

  (*
   * ERC20: Sets amount as the allowance of spender over the caller’s tokens.
   *
   * Returns a boolean value (and the new state) indicating whether the
   * operation succeeded.
   *
   * @type: ($state, ADDR, ADDR, Int) => $result;
   *)
  approve(state, sender, spender, amount) ==
    LET err ==
      CASE ~(sender /= ZERO_ADDRESS) -> "ERC20: transfer from the zero address"
        [] ~(spender /= ZERO_ADDRESS) -> "ERC20: transfer to the zero address"
        [] OTHER -> ""
    IN
    IF err /= ""
    THEN Error(err)
    ELSE
      \* the case of sender == spender seems to be allowed
      Ok(TRUE, [ state EXCEPT !.allowance[sender, spender] = amount ])

  (*
   * Moves amount tokens from `fromAddr` to `toAddr` using the allowance mechanism.
   * amount is then deducted from the caller’s allowance.
   *
   * Returns a boolean value indicating whether the operation succeeded.
   *
   *
   * @type: ($state, ADDR, ADDR, ADDR, Int) => $result;
   *)
  transferFrom(state, sender, fromAddr, toAddr, amount) ==
    \* _spendAllowance
    LET currentAllowance == state.allowance[fromAddr, sender] IN
    LET err ==
      CASE ~(currentAllowance >= amount) -> "ERC20: insufficient allowance"
        [] ~(fromAddr /= ZERO_ADDRESS) -> "ERC20: approve from the zero address"
        [] ~(toAddr /= ZERO_ADDRESS) -> "ERC20: approve to the zero address"
        [] OTHER -> ""
    IN
    LET updatedState ==
      IF currentAllowance = MAX_UINT
      THEN state
      ELSE [ state EXCEPT !.allowance[fromAddr, sender] = @ - amount ]
    IN
    IF err /= ""
    THEN Error(err)
    ELSE _transfer(updatedState, fromAddr, toAddr, amount)

  (****************************************************************
   * PROPERTIES that do not belong too the original EIP20 spec,
   * but they should hold true.
   ****************************************************************)

  \* Compute the sum over all balances.
  \*
  \* @type: (ADDR -> Int) => Int;
  sumOverBalances(balances) ==
    LET \* @type: (Int, ADDR) => Int;
      Add(sum, addr) == sum + balances[addr]
    IN
    \* NOTE: we could use FiniteSetsExt!FoldSet from the community modules.
    \* https://github.com/tlaplus/CommunityModules/blob/a206a33c7e40a75beb06554482bde26b8f40d5f4/modules/FiniteSetsExt.tla#L7-L14
    \* We just did not want to copy one more module.
    ApaFoldSet(Add, 0, DOMAIN balances)

  \* The total supply, as stored in the state,
  \* is equal to the sum of amounts over all balances.
  \*
  \* @type: $state => Bool;
  isTotalSupplyCorrect(state) ==
    sumOverBalances(state.balanceOf) = state.totalSupply

  \* Zero address should not carry coins.
  \*
  \* @type: $state => Bool;
  isZeroAddressEmpty(state) ==
    state.balanceOf[ZERO_ADDRESS] = 0

  \* There are no overflows in totalSupply, balanceOf, and approve.
  \*
  \* @type: $state => Bool;
  isNoOverflows(state) ==
    /\ isUint(state.totalSupply)
    /\ \A a \in DOMAIN state.balanceOf:
         isUint(state.balanceOf[a])
    /\ \A p \in DOMAIN state.allowance:
         isUint(state.allowance[p])

================================================================================