// Copyright 2014 Dawid Ciężarkiewicz
// See LICENSE file for more information

//! Hexagonal map operations
//!
//! A lot of ideas taken from [redbloggames hexagon page][hexagon]
//!
//! [hexagon]: http://www.redblobgames.com/grids/hexagons/

// TODO:
// Implement Eq between (i, i) and (i, i, i) by using to_coordinate

#![crate_name = "hex2d"]
#![crate_type = "lib"]

#![warn(missing_docs)]
#![allow(unstable)]

extern crate num;
extern crate rand;

use std::num::{SignedInt, FromPrimitive, ToPrimitive, Float};
use std::ops::{Add, Neg, Sub};
use std::cmp::{max, min};
use num::integer::{Integer};

use Direction::*;
use Angle::*;
use Spin::*;
use Spacing::*;

#[cfg(test)]
mod test;

/// Cube Coordinateinates on 2d hexagonal grid
///
/// Point-topped:
///
/// ```norust
///
///           /\
///         /    \
///        |      |
///        |      |
///         \    /
///           \/
///
///            -z
/// +y     YZ  |  XZ     +x
///  ---       |       ---
///     ---    |    ---
///        --- | ---
///   YX      -x-    XY
///        --- | ---
///     ---    |    ---
///  ---   ZX  |  ZY   ---
/// -x         |          -y
///            +z
///  ```
///
/// Flat-topped:
///
/// ```norust
///            ____
///           /    \
///          /      \
///          \      /
///           \____/
///
///        +y       -z
///         \       /
///          \ YZ  /
///       YX  \   /  XZ
///            \ /
///   -x--------x--------+x
///            / \
///       ZX  /   \ XY
///          /  ZY \
///         /       \
///        +z       -y
///  ```
///
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Coordinate<I : SignedInt = i32> {
    /// `x` coordinate
    pub x : I,
    /// `y` coordinate
    pub y : I,
    /// `z` coordinate
    pub z : I,
}

/// Can be treated as a `Coordinate`
pub trait ToCoordinate<I : SignedInt = i32> {
    /// Convert to `Coordinate` part of this data
    fn to_coordinate(&self) -> Coordinate<I>;
}

/// Can be treated as a `Angle`
pub trait ToAngle {
    /// Convert to `Angle` part of this data
    fn to_angle(&self) -> Angle;
}

/// Direction between `Coordinate`s
///
/// See `Coordinate` for graph with directions.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Direction {
    /// +Y -Z
    YZ = 0,
    /// -Z +X
    XZ,
    /// +X -Y
    XY,
    /// -Y +Z
    ZY,
    /// +Z -X
    ZX,
    /// -X +Y
    YX,
}

// Use Direction::all() instead
static ALL_DIRECTIONS : [Direction; 6] = [ YZ, XZ, XY, ZY, ZX, YX ];

/// Angle, relative to a Direction
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Angle {
    /// 0deg
    Forward = 0,
    /// 60deg
    Right,
    /// 120deg
    RightBack,
    /// 180deg
    Back,
    /// 240deg
    LeftBack,
    /// 300deg
    Left,
}

/// Spinning directions
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Spin {
    /// Clockwise
    CW(Direction),
    /// Counterclockwise
    CCW(Direction),
}

/// Floating point tile size for pixel conversion functions
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Spacing {
    /// Hex-grid with an edge on top
    FlatTop(f32),
    /// Hex-grid with a corner on top
    PointyTop(f32),
}

/// Integer pixel tile size for integer pixel conversion functions
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum IntegerSpacing<I> {
    /// Hex-grid with an edge on top
    FlatTop(I, I),
    /// Hex-grid with a corner on top
    PointyTop(I, I),
}

impl<I : SignedInt+FromPrimitive+Integer> Coordinate<I> {
    /// Create new Coord from `x` and `y`
    pub fn new(x : I, y : I) -> Coordinate<I> {
        Coordinate { x: x, y: y, z: -x - y }.invariant()
    }

    /// Check invariants
    fn invariant(&self) -> Coordinate<I> {
        debug_assert!(self.x + self.y == - self.z);
        *self
    }

    /// Scale coordinate by a factor `s`
    pub fn scale(&self, s : I) -> Coordinate<I> {
        let x = self.x * s;
        let y = self.y * s;
        Coordinate{ x: x, y: y, z: -x - y}.invariant()
    }

    /// Array with all the neighbors of a coordinate
    pub fn neighbors(&self) -> [Coordinate<I>; 6] {
        [
            *self + YZ,
            *self + XZ,
            *self + XY,
            *self + ZY,
            *self + ZX,
            *self + YX,
        ]
    }

    /// Distance between two Coordinates
    pub fn distance(&self, c : Coordinate<I>) -> I {
        ((self.x - c.x).abs() + (self.y - c.y).abs() + (self.z - c.z).abs()) / FromPrimitive::from_i8(2).unwrap()
    }

    /// All coordinates in radius `r`
    pub fn range(&self, r : I) -> Vec<Coordinate<I>> {

        let mut res = vec!();
        self.for_each_in_range(r, |c| res.push(c));

        res
    }
/*
    pub fn range(&self, r : I) -> Vec<Coordinate<I>> {
        let mut res = vec!();
        let one : I = FromPrimitive::from_i8(1).unwrap();

        for x in range(-r, r + one) {
            for y in range(max(-r, -x-r), min(r, -x+r) + one) {
                let z = -x - y;
                res.push(Coordinate{ x: x, y: y, z: z}.invariant());
            }
        }

        res
    }*/


    /// Execute `f` for all coordinates in radius `r`
    pub fn for_each_in_range<F>(&self, r : I, mut f : F)
        where F : FnMut(Coordinate<I>) {
        let one : I = FromPrimitive::from_i8(1).unwrap();

        for x in range(-r, r + one) {
            for y in range(max(-r, -x-r), min(r, -x+r) + one) {
                let z = -x - y;
                f(Coordinate{
                    x: self.x + x,
                    y: self.y + y,
                    z: self.z + z
                }.invariant());
            }
        }
    }

    /// A ring of radius `r`, starting in a corner in a given Direction
    ///
    /// Example: Elements in order for Ring of radius 2, Direction ZX, CCW
    ///
    /// ```norust
    ///
    ///              8
    ///            9   7
    ///         10   .   6
    ///            .   .
    ///         11   x   5
    ///            .   .
    ///          0   .   4
    ///            1   3
    ///              2
    ///
    pub fn ring(&self, r : i32, s : Spin) -> Vec<Coordinate<I>> {
        let mut res = vec!();
        self.for_each_in_ring(r, s, |c| res.push(c));

        res
    }

    /// Call `f` for each coordinate in a ring
    ///
    /// See `ring` for a ring description.
    pub fn for_each_in_ring<F>(&self, r : i32, s : Spin, mut f : F)
        where F : FnMut(Coordinate<I>) {

        if r == 0 {
            f(*self);
            return;
        }

        let (start_angle, step_angle, start_dir) = match s {
            CW(d) => (RightBack, Right, d),
            CCW(d) => (LeftBack, Left, d),
        };


        let mut cur_coord = *self + start_dir.to_coordinate().scale(
            FromPrimitive::from_i32(r).unwrap()
            );
        let mut cur_dir = start_dir + start_angle;

        for _ in range(0, 6) {
            let cur_dir_coord = cur_dir.to_coordinate();
            for _ in range(0, r) {
                f(cur_coord);
                cur_coord = cur_coord + cur_dir_coord;
            }
            cur_dir = cur_dir + step_angle;
        }
    }

    /// Convert to pixel coordinates using `spacing`, where the
    /// parameter means the edge length of a hexagon.
    ///
    /// This function is meant for graphical user interfaces
    /// where resolution is big enough that floating point calculation
    /// make sense.
    pub fn to_pixel_float(&self, spacing : Spacing) -> (f32, f32) {
        let q = self.x.to_f32().unwrap();
        let r = self.z.to_f32().unwrap();
        match spacing {
            FlatTop(s) => (
                s * 3f32 / 2f32 * q,
                s * 3f32.sqrt() * (r + q / 2f32)
                ),
            PointyTop(s) => (
                s * 3f32.sqrt() * (q + r / 2f32),
                s * 3f32 / 2f32 * r
                )
        }
    }

    /// Convert to integer pixel coordinates using `spacing`, where the
    /// parameters mean the width and height multiplications
    pub fn to_pixel_integer(&self, spacing : IntegerSpacing<I>) -> (I, I) {
        let q = self.x;
        let r = self.z;
        let two = FromPrimitive::from_i8(2).unwrap();

        match spacing {
            IntegerSpacing::FlatTop(w, h) => (
                w * q,
                h * (r + r + q) / two
                ),
            IntegerSpacing::PointyTop(w, h) => (
                w * (q + q + r) / two,
                h * r
                )
        }
    }

    /// Convert integer pixel coordinates `v` using `spacing` to nearest coordinate that has both
    /// integer pixel coordinates lower or equal to `v`. Also return offset (in integer pixels)
    /// from that coordinate.
    // Took me a while to figure this out, but it seems to work. Brilliant.
    pub fn from_pixel_integer(spacing : IntegerSpacing<I>, v : (I, I)) -> (Coordinate<I>, (I, I)) {
        let (asc_x, asc_y) = v;

        let two : I = FromPrimitive::from_i8(2).unwrap();

        let ((q, qo),(r, ro)) = match spacing {
            IntegerSpacing::FlatTop(w, h) => (
                (asc_x.div_floor(&w), asc_x.mod_floor(&w)),
                (
                    (asc_y - h * asc_x.div_floor(&w) / two).div_floor(&h),
                    (asc_y + h / two * asc_x.div_floor(&w)).mod_floor(&h)
                )
                ),
            IntegerSpacing::PointyTop(w, h) => (
                (
                    (asc_x - w * asc_y.div_floor(&h) / two).div_floor(&w),
                    (asc_x + w / two * asc_y.div_floor(&h)).mod_floor(&w)
                ),
                (asc_y.div_floor(&h),  asc_y.mod_floor(&h))
                ),
        };

        let coord = Coordinate{ x: q, y: -q - r, z: r };
        (coord, (qo, ro))
    }
}

impl<I : SignedInt> ToCoordinate<I> for Coordinate<I> {
    fn to_coordinate(&self) -> Coordinate<I> {
        *self
    }
}


impl<I : SignedInt+FromPrimitive+Integer> ToCoordinate<I> for (I, I) {
    fn to_coordinate(&self) -> Coordinate<I> {
        let (x, y) = *self;
        Coordinate::new(x, y)
    }
}

impl<I : SignedInt+FromPrimitive+Integer> ToCoordinate<I> for Direction {
    fn to_coordinate(&self) -> Coordinate<I> {
        let (x, y, z) = match *self {
            YZ => (0, 1, -1),
            XZ => (1, 0, -1),
            XY => (1, -1, 0),
            ZY => (0, -1, 1),
            ZX => (-1, 0, 1),
            YX => (-1, 1, 0),
        };

        Coordinate {
            x: FromPrimitive::from_i8(x).unwrap(),
            y: FromPrimitive::from_i8(y).unwrap(),
            z: FromPrimitive::from_i8(z).unwrap()
        }.invariant()
    }
}


impl<I : SignedInt+FromPrimitive+Integer, T: ToCoordinate<I>> Add<T> for Coordinate<I> {
    type Output = Coordinate<I>;

    fn add(self, c : T) -> Coordinate<I> {
        let c = c.to_coordinate();

        Coordinate {
            x: self.x + c.x,
            y: self.y + c.y,
            z: self.z + c.z,
        }.invariant()
    }
}

impl<I : SignedInt+FromPrimitive+Integer, T: ToCoordinate<I>> Sub<T> for Coordinate<I> {
    type Output = Coordinate<I>;

    fn sub(self, c : T) -> Coordinate<I> {
        let c = c.to_coordinate();

        Coordinate {
            x: self.x - c.x,
            y: self.y - c.y,
            z: self.z - c.z,
        }.invariant()
    }
}

impl<I : SignedInt+FromPrimitive+Integer> Neg for Coordinate<I> {
    type Output = Coordinate<I>;

    fn neg(self) -> Coordinate<I> {
        Coordinate { x: -self.x, y: -self.y, z: -self.z }.invariant()
    }
}

impl Direction {
    /// Static array of all directions
    pub fn all() -> &'static [Direction; 6] {
        &ALL_DIRECTIONS
    }

    /// From integer
    ///
    /// This should probably be internal
    pub fn from_int<I : Integer+FromPrimitive+ToPrimitive>(i : I) -> Direction {
        match i.mod_floor(&FromPrimitive::from_i8(6).unwrap()).to_u8().unwrap() {
            0 => YZ,
            1 => XZ,
            2 => XY,
            3 => ZY,
            4 => ZX,
            5 => YX,
            _ => panic!()
        }
    }

    /// Convert to integer
    ///
    /// This should probably be internal
    pub fn to_int<I : Integer+FromPrimitive>(&self) -> I {
       FromPrimitive::from_u8(*self as u8).unwrap()
    }
}

impl Angle {
    /// From integer
    ///
    /// This should probably be internal
    pub fn from_int<I : Integer+FromPrimitive+ToPrimitive>(i : I) -> Angle {
        match i.mod_floor(&FromPrimitive::from_i8(6).unwrap()).to_u8().unwrap() {
            0 => Forward,
            1 => Right,
            2 => RightBack,
            3 => Back,
            4 => LeftBack,
            5 => Left,
            _ => panic!()
        }
    }

    /// Convert to integer
    ///
    /// This should probably be internal
    pub fn to_int<I : Integer+FromPrimitive>(&self) -> I {
       FromPrimitive::from_u8(*self as u8).unwrap()
    }
}

impl ToAngle for Angle {
    fn to_angle(&self) -> Angle {
        *self
    }
}

impl<T: ToAngle> Add<T> for Direction {
    type Output = Direction;

    fn add(self, c : T) -> Direction {
        let c = c.to_angle();

        Direction::from_int(self.to_int::<i32>() + c.to_int())
    }
}

