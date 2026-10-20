# NI observation execution

This directory contains the first, memory-only part of the NI execution add-on.
It reuses Vellvm's denotation, memory interpreter and fused dispatcher unchanged.
It is not yet the complete NI observable semantics or a security test oracle.
There is no taint tracker or experiment verdict here.

For example, a request to load from unallocated address `p` records
`OLoad ty p`, then returns `Stopped [OLoad ty p] UB`. The observation remains
available even though the original Vellvm computation has no normal return.

## Build and check

After building the existing genllvm/Vellvm dependencies, compile NI for
interactive reading in Emacs or VsRocq from the genllvm root:

```sh
opam exec --switch=genllvm -- make -C ni
```

This uses `ni/_RocqProject` and writes `.vo` files beside the NI sources, with
the usual `.vos`/`.vok` markers. It compiles the listed definitions, proofs and
test modules without extracting OCaml or running benchmarks. The editor must
use the `genllvm` switch and the load paths in `ni/_RocqProject`.
`make -C ni clean` removes NI build artifacts, leaving dependency builds alone.

For the separate scratch validation and benchmark:

```sh
opam exec --switch=genllvm -- make -C ni check
opam exec --switch=genllvm -- make -C ni bench
```

Both commands create a fresh directory under `/tmp`, copy sources without `.vo`
files, build the required Vellvm dependencies, compile the preservation proofs
and runner examples, extract OCaml and run the fixtures. All build artifacts stay
in that directory. Its path is printed and kept for inspection. Neither command
installs packages or changes Vellvm/general generator sources.

The `genllvm` switch must already contain this checkout's dependencies, including
Rocq 9.1.1 and QuickChick 2.2.0. The extraction entry imports `QCExtractionFix.v`.
For measurement arguments:

```sh
opam exec --switch=genllvm -- python3 ni/check.py --benchmark --count 2000 --repeats 5
```

The logs include source hashes, revisions, commands, tool versions, proof
assumptions, fixture output and per-run diagnostics. A failed command or fixture
returns a nonzero status. The benchmark adds raw CSV, a JSON summary and a
process resource log. Peak RSS covers all methods in the shared process;
it is not a per-method overhead measurement.

## Execution flow

```text
stock program denotation
  -> stock intrinsic pass (may emit memory requests)
  -> memory_handler
       Load/Store: Observe payload, then stock interp_vellvm_h
       other requests: stock interp_vellvm_h
  -> itree (ObservationE memory_observation +' MCFGEbot) (FusedS * value)
  -> run: collect observations; return Normal / Stopped / OutOfFuel
```

`FusedS` stays unchanged. The collector keeps the trace in its own argument,
using cons during execution and a single linear `rev_append` at each outcome.
The original handler is called through a thunk (`unit -> itree ...`) so OCaml
does not compute a failing memory operation before delivering its observation.

| File | Responsibility |
|---|---|
| `rocq/Semantics/Observation.v` | Generic observation transport, delivery, erasure and `before` wrapper |
| `rocq/Semantics/MemoryObservation.v` | Select Load/Store requests and form payloads |
| `rocq/Semantics/MemoryExecution.v` | Reuse the original dispatcher and program entry |
| `rocq/Semantics/Runner.v` | Fuel, trace collection and residual-event outcomes |
| `rocq/Semantics/Preservation.v` | Erasure laws through the state interpreter and program entry |
| `rocq/Tests/` | Runner examples, memory fixtures, extraction and benchmark controls |
| `ml/` | Fixture and benchmark drivers only |

Delivery and collection are separate. `memory_handler` accepts the delivery
function, while `before` accepts the computation to execute. Changing how a
notification is delivered does not require rewriting the memory operation.

## Contracts

- A Load/Store observation records the access `dtyp` and full request `dvalue`
  address, including malformed addresses. It does not contain the stored value.
- Observations precede the original handler, including requests that fail and
  zero-byte Stores. Setup, global initialization and frame Stores are included.
- A positive fuel budget processes one `Ret`, `Tau` or `Vis`, including an
  observation or terminal event. Zero returns `OutOfFuel` without inspecting the
  tree. After the last continuing `Vis`, the collector does not evaluate its
  continuation. Creating the input tree and computing one node/primitive are not
  bounded by this counter.
- Original UB, OOM, general Failure and LLVM exceptions remain distinct. External
  calls and program stdout/stderr stop with dedicated reasons; no response value
  is invented. Debug always resumes with `tt`, consumes one fuel step, and adds
  no observation. There is no Debug policy argument or Debug stop category.
- No `StopE` is added. Extracted diagnostic output is captured separately from
  the semantic trace. The fixture driver labels runs and the harness checks
  message association, including a cutoff that must not print a later UB.
- The extraction used here maps `nat` to OCaml `int` through QuickChick. OCaml
  callers must supply nonnegative, representable fuel; the benchmark checks its
  arguments. Choosing a later public runner interface remains separate.

`erase_interpreter_memory_gen` proves that removing only the added observation
events gives an `eutt`-equivalent original `interpreter_gen`, including its return
state/value and all original residual events. This proof is for the memory-only
entry. It does not prove trace completeness, equal finite-fuel outcomes, or
equivalence of extracted diagnostic side effects. The build records inherited
library axioms; the add-on introduces no axioms, `Admitted`, or disabled guard
checking.

## Validation and limits

Seven kernel-checked runner examples cover positive/zero fuel, terminal handling,
loop prefixes and trace ordering. Nineteen extracted fixtures cover actual
Load/Store execution, failure prefixes, invalid addresses, zero-byte stores,
intrinsic-produced requests, setup/global/frame Stores, access widths, residual
categories and Debug resumption/fuel boundaries. OOM coverage uses an original `raiseOOM` event;
it does not force a real allocation failure. Full memory fixtures are executed
after extraction; they are not claimed as kernel-computed boolean proofs.

The benchmark compares bounded stock execution, delivery disabled, delivery with
trace discarded, and full collection on memory and local-variable workloads.
Each timed run constructs a fresh workload and must finish normally with the
expected result and trace length. These are measurement controls, not NI oracles;
the timings do not measure a complete generated-program campaign.

Branch, switch, call-target and selected binary observations remain to be added
at their producers. Bulk-intrinsic internal byte operations are not fabricated
as Load/Store requests. For example, a branch-only function currently has no
branch observation: correct memory erasure alone does not make its NI trace
complete. Do not use this entry to issue NI verdicts yet.
