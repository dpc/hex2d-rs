[![Build Status](https://travis-ci.org/dpc/hex2d-rs.svg?branch=master)](https://travis-ci.org/dpc/hex2d-rs)

# hex2d

## Introduction

Library for working with 2d hex map systems.

It might be lame, I've hacked it together for a toy game. But patches are
always welcome. :)

To get some overview see [examples/simple.rs](examples/simple.rs).

The coordinate system is supposed to be similar to the one used usually on
screens, which means y grows "downward" (well, southwest, really).

	    (0,0) ----> x
	     /   /N \
	    /  NW\__/NE
	   /  \__/  \__
	  /   /SW\__/SE
	 v       /S \__
	y

Read [Documentation](http://www.rust-ci.org/dpc/hex2d-rs/doc/hex2d/) for details.

## Building

	cargo build

Run example:

	cargo run --example simple
