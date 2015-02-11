[![Build Status](https://travis-ci.org/dpc/hex2d-rs.svg?branch=master)](https://travis-ci.org/dpc/hex2d-rs)

# hex2d

## Introduction

Library for working with 2d hex map systems.

A lot of ideas taken from [redbloggames hexagon page][hexagon]

[hexagon]: http://www.redblobgames.com/grids/hexagons/
[hex2d-rs]: http://github.com/dpc/hex2d-rs
[hex2d-dpcext-rs]: http://github.com/dpc/hex2d-dpcext-rs

Read [Documentation](//dpc.github.io/hex2d-rs/) for details.

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
