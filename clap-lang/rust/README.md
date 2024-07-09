# Rust Clap implementation

## About

This directory contains the Rust code for Clap, an eDSL for building Plonkish circuits.

This codebase is experimental, not meant for poduction use.

## Code structure

The implementation is split into two subcrates: `base` and `builder`.

The `base` crate defines the core functionality of Clap. This includes:

- `expr.rs`: types and traits for gates, constrained vectors and context.
- `circuit.rs`: circuit representation and main functions.
- `table.rs`: logic for tabulation.
- `optimizer.rs`: circuit optimizer.
- `gate_*.rs`: gate implementation.
- `cs_*.rs`: constrained vector implementations.

The `builder` crate, in turn, contains the builder (primitives used to describe circuits) and some circuit implementations.

## Running

The `main.rs` file contains tests for all the circuits we defined.
The command `cargo test` runs them all.
