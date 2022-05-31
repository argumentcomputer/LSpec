# LSpec

A Testing Framework for Lean

## Usage

There are two ways to use LSpec: via the `#lspec` command and via the `lspec`
function.

The former is used when you want to test a function in the same file you define
it. If the test fails, an error is thrown, which can interrupt the `lake build`
command in your lib that uses LSpec as a dependency.

The later is meant for writing tests on a separate file, which can then be run
independently with the `lspec` binary. We'll see more about it.

## The `LSpec` and `Rel` types

### The `it` helper function

## The `#lspec` command

## The `lspec` function
