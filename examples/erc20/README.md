# Specifying the ERC20 interface and mempool

This directory contains several TLA+ specifications related to the
[ERC20 token][]:

 - [erc20.tla][] is a specification of the ERC20
   that follows the implementation of [ERC20 by OpenZeppelin][].
   It does not specify a state machine, but it specifies the reusable
   logic of ERC20.

 - [erc20_tests.tla][] is a state machine that we use to show that:

   - ERC20 preserves its initial total supply, see [totalSupplyInv][],
   - ERC20 does not transfer to the address `0x0`, see [zeroAddressInv][],
   - ERC20 does not overflow the account balances, see [noOverflowInv][].
   - Method `transfer` satisfies the intuitive post-condition,
     see [transferPrePost][].

 - [erc20_mempool.tla][] is a state machine that models the interaction with an
 ERC20 contract via mempool, that is, when the methods are called by external
 users. We use this state machine to demonstrate how to detect the well-known
 issue with the order of `transferFrom` and `approve`, see the [issue #20][].

These specifications were produced out of the Quint specification [erc20.qnt][]
by hand. While doing this translation, we made our best to use the more
expressive constructs of TLA+ such as nested EXCEPTs. Hence, you can use these
two specifications to compare the syntax of Quint with the syntax of TLA+.


[ERC20 by OpenZeppelin]: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/token/ERC20/ERC20.sol
[totalSupplyInv]: https://github.com/informalsystems/tla-apalache-workshop/blob/0f13bf0547ca7f8c3f9b6ccdcd0c90b940d1a9a5/examples/erc20/erc20_tests.tla#L54
[zeroAddressInv]: https://github.com/informalsystems/tla-apalache-workshop/blob/0f13bf0547ca7f8c3f9b6ccdcd0c90b940d1a9a5/examples/erc20/erc20_tests.tla#L56
[noOverflowInv]: https://github.com/informalsystems/tla-apalache-workshop/blob/0f13bf0547ca7f8c3f9b6ccdcd0c90b940d1a9a5/examples/erc20/erc20_tests.tla#L58
[transferPrePost]: https://github.com/informalsystems/tla-apalache-workshop/blob/0f13bf0547ca7f8c3f9b6ccdcd0c90b940d1a9a5/examples/erc20/erc20_tests.tla#L83-L105
[issue #20]: https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
[erc20.qnt]: https://github.com/informalsystems/quint/tree/main/examples/solidity/ERC20
[Quint]: https://github.com/informalsystems/quint