# hex2d

<p align="center">
  <a href="https://travis-ci.org/dpc/hex2d-rs">
      <img src="https://img.shields.io/travis/dpc/hex2d-rs/master.svg?style=flat-square" alt="Build Status">
  </a>
  <a href="https://crates.io/crates/hex2d">
      <img src="http://meritbadge.herokuapp.com/hex2d?style=flat-square" alt="crates.io">
  </a>
  <img src="https://img.shields.io/badge/GITTER-join%20chat-green.svg?style=flat-square" alt="Gitter Chat">
  <br>
  <strong><a href="https://docs.rs/hex2d">Documentation</a></strong>
</p>


## Introduction

Library for working with 2d hex map systems.

A lot of ideas taken from [redbloggames hexagon page][hexagon]

[hexagon]: http://www.redblobgames.com/grids/hexagons/
[hex2d-rs]: http://github.com/dpc/hex2d-rs
[hex2d-dpcext-rs]: http://github.com/dpc/hex2d-dpcext-rs

Read [Documentation](https://docs.rs/hex2d) for details.

See [issues](//github.com/dpc/hex2d-rs/issues/) for TODO and BUGs.

You might be interested in additional functionality provided by [hex2d-dpcext-rs] library.

### Coordinate system

Pointy-topped:

              /\
            /    \
           |      |
           |      |
            \    /
              \/

              -z
    +y     YZ  |  XZ     +x
     ---       |       ---
        ---    |    ---
           --- | ---
      YX      -x-    XY
           --- | ---
        ---    |    ---
     ---   ZX  |  ZY   ---
    -x         |          -y
              +z

Flat-topped:

             ____
            /    \
           /      \
           \      /
            \____/

         +y       -z
          \       /
           \ YZ  /
        YX  \   /  XZ
             \ /
    -x--------x--------+x
             / \
        ZX  /   \ XY
           /  ZY \
          /       \
         +z       -y

## Building

    cargo build
    
    
## Verification Recommendation

To help with the maintaince, the ownership of this crate is potentially shared between multiple developers.
It is recommend to always use [cargo-crev](https://github.com/crev-dev/cargo-crev/tree/master/cargo-crev)
to verify trustworthiness of each of your dependencies, including this one.
