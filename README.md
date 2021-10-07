# Thinking about protocols with TLA+ and Apalache

We are introducing TLA+ and the model checker
[Apalache](https://apalache.informal.systems). Prior knowledge of TLA+
is not required.

## 1. Step-by-step instructions

### 1.1. Setup

If you want to reproduce the steps, make sure that you have installed
the following tools first:

 - Apalache version 0.16.5. Check [Apalache releases][].
 - **optional**: [TLA Toolbox][] or [VScode plugin for TLA+][]

### 1.2. Incremental specification of clock synchronization

Material for the [TLA+ tutorial](http://conf.tlapl.us/202110/),
co-located with [DISC 2021](http://www.disc-conference.org/wp/disc2021/).

Check the specifications in [clock-sync](examples/clock-sync)
and the extended version of the tutorial (TBA). Follow the
[clock sync: step-by-step instructions][].

### 1.3. Incremental specification of token transfer

Material for the workshop at [HackAtom RU 2021][].

Follow the [token transfer: step-by-step instructions][].

**WARNING**: The final specification
[TokenTransfer10.tla](./examples/token-transfer/TokenTransfer10.tla) is **not** a
complete specification of [ICS20][].  If you want to specify [ICS20][],
you have to introduce the following missing features:

 - acknowledgments.

## 2. Learning more about TLA+
 
 - [Apalache model checker][]
 - [TLA+ Home Page][]
 - [TLA+ Video Course][]
 - [Specifying Systems][]
 - [TLA+ language manual for engineers][]
 - [LearnTla.com][]
 - [Community Modules][]
 - [TLC model checker][]
 - [TLA+ examples][]
    

[TLA+ examples]: https://github.com/tlaplus/examples
[TLA+ language manual for engineers]: https://apalache.informal.systems/docs/lang/index.html
[Apalache model checker]: https://apalache.informal.systems
[TLC model checker]: http://lamport.azurewebsites.net/tla/tools.html
[Summary of TLA]: https://lamport.azurewebsites.net/tla/summary.pdf
[TLA+ Home Page]: http://lamport.azurewebsites.net/tla/tla.html
[Specifying Systems]: http://lamport.azurewebsites.net/tla/book.html?back-link=learning.html
[Community Modules]: https://github.com/tlaplus/CommunityModules
[LearnTla.com]: https://learntla.com
[TLA+ Video Course]: http://lamport.azurewebsites.net/video/videos.html
[TLA Toolbox]: https://lamport.azurewebsites.net/tla/toolbox.html
[VScode plugin for TLA+]: https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus
[Building Apalache from source]: https://apalache.informal.systems/docs/apalache/installation/source.html
[Apalache releases]: https://github.com/informalsystems/apalache/releases
[token transfer: step-by-step instructions]: ./docs/token-transfer-steps.md 
[clock sync: step-by-step instructions]: ./docs/clock-sync-steps.md 
[ICS20]: https://github.com/cosmos/ibc/tree/master/spec/app/ics-020-fungible-token-transfer
[HackAtom RU 2021]: https://blog.cosmos.network/hackatom-ru-2021-buckle-up-cosmonauts-we-have-no-problems-and-are-ready-for-takeoff-69c59812b2eb
