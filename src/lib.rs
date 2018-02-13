// Copyright 2014 Dawid Ciężarkiewicz
// See LICENSE file for more information

//! Hexagonal map operations utility library
//!
//! A lot of ideas taken from [redbloggames hexagon page][hexagon]
//!
//! [hexagon]: http://www.redblobgames.com/grids/hexagons/
//!
//! Pointy-topped:
//!
//! ```text
//!           /\
//!         /    \
//!        |      |
//!        |      |
//!         \    /
//!           \/
//!
//!            -z
//! +y     YZ  |  XZ     +x
//!  ---       |       ---
//!     ---    |    ---
//!        --- | ---
//!   YX      -x-    XY
//!        --- | ---
//!     ---    |    ---
//!  ---   ZX  |  ZY   ---
//! -x         |          -y
//!            +z
//! ```
//!
//! Flat-topped:
//!
//! ```text
//!            ____
//!           /    \
//!          /      \
//!          \      /
//!           \____/
//!
//!        +y       -z
//!         \       /
//!          \ YZ  /
//!       YX  \   /  XZ
//!            \ /
//!   -x--------x--------+x
//!            / \
//!       ZX  /   \ XY
//!          /  ZY \
//!         /       \
//!        +z       -y
//! ```
//!

// TODO:
// Implement Eq between (i, i) and (i, i, i) by using to_coordinate

#![crate_name = "hex2d"]
#![crate_type = "lib"]

#![warn(missing_docs)]

extern crate num;
extern crate rand;
#[cfg(feature="serde-serde")]
extern crate serde;
#[cfg(feature="serde-serde")]
#[macro_use]
extern crate serde_derive;

use num::{Float, One, Zero};
use num::iter::range_inclusive;
use std::ops::{Add, Sub, Neg};
use std::cmp::{max, min};
use std::f64::consts::PI;

pub use Direction::*;
pub use Angle::*;
use Spin::*;
use Spacing::*;


/// Integer trait required by this library
pub trait Integer : num::Signed +
                    num::Integer +
                    num::CheckedAdd +
                    num::ToPrimitive +
                    num::FromPrimitive +
                    One + Zero + Copy { }

impl<I> Integer for I
where
I : num::Signed +
    num::Integer +
    num::CheckedAdd +
    num::ToPrimitive +
    num::FromPrimitive +
    One + Zero + Copy { }

#[cfg(test)]
mod test;

/// Coordinate on 2d hexagonal grid
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
pub struct Coordinate<I : Integer = i32> {
    /// `x` coordinate
    pub x : I,
    /// `y` coordinate
    pub y : I,
}

/// Can be treated as a `Coordinate`
pub trait ToCoordinate<I: Integer = i32> {
    /// Convert to `Coordinate` part of this data
    fn to_coordinate(&self) -> Coordinate<I>;
}

/// Can be treated as a `Direction`
pub trait ToDirection {
    /// Convert to `Angle` part of this data
    fn to_direction(&self) -> Direction;
}


/// Position on 2d hexagonal grid (Coordinate + Direction)
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
pub struct Position<I : Integer = i32> {
    /// `x` coordinate
    pub coord : Coordinate<I>,
    /// `y` coordinate
    pub dir : Direction,
}

/// Direction on a hexagonal map
///
/// See `Coordinate` for graph with directions.
///
/// Naming convention: increasing coordinate for a given direction is first
/// decreasing is second. The missing coordinate is unaffected by a move in
/// a given direction.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
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
static ALL_ANGLES : [Angle; 6] = [ Forward, Right, RightBack, Back, LeftBack, Left];

/// Angle, relative to a Direction
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
pub enum Angle {
    /// 0deg clockwise
    Forward = 0,
    /// 60deg clockwise
    Right,
    /// 120deg clockwise
    RightBack,
    /// 180deg clockwise
    Back,
    /// 240deg clockwise
    LeftBack,
    /// 300deg clockwise
    Left,
}

/// Spinning directions
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
pub enum Spin {
    /// Clockwise
    CW(Direction),
    /// Counterclockwise
    CCW(Direction),
}

/// Floating point tile size for pixel conversion functions
#[derive(Copy, Clone, PartialEq, Debug, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
pub enum Spacing {
    /// Hex-grid with an edge on top
    FlatTop(f32),
    /// Hex-grid with a corner on top
    PointyTop(f32),
}

/// Integer pixel tile size for integer pixel conversion functions
///
/// Example values that give good results:
///
/// * FlatTop(3, 2)
/// * PointyTop(2, 1)
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
pub enum IntegerSpacing<I> {
    /// Hex-grid with an edge on top
    FlatTop(I, I),
    /// Hex-grid with a corner on top
    PointyTop(I, I),
}

impl<I : Integer> Coordinate<I> {
    /// Create new Coord from `x` and `y`
    pub fn new(x : I, y : I) -> Coordinate<I> {
        Coordinate { x: x, y: y}
    }

    /// Old name for `nearest`
    #[deprecated(note="use `nearest` instead")]
    pub fn from_round(x : f32, y : f32) -> Coordinate<I> {
        Coordinate::nearest(x, y)
    }

    /// Round x, y float to nearest hex coordinates
    pub fn nearest(x : f32, y : f32) -> Coordinate<I> {
        let z = 0f32 - x - y;

        let mut rx = x.round();
        let mut ry = y.round();
        let rz = z.round();

        let x_diff = (rx - x).abs();
        let y_diff = (ry - y).abs();
        let z_diff = (rz - z).abs();

        if x_diff > y_diff && x_diff > z_diff {
            rx = -ry - rz;
        } else if y_diff > z_diff {
            ry = -rx - rz;
        } else {
            // not needed, kept for a reference
            // rz = -rx - ry;
        }

        Coordinate {
            x: num::FromPrimitive::from_f32(rx).unwrap(),
            y: num::FromPrimitive::from_f32(ry).unwrap(),
        }
    }

    /// Old name for `nearest_lossy`
    #[deprecated(note="use `nearest_lossy` instead")]
    pub fn from_round_lossy(x : f32, y : f32) -> Option<Coordinate<I>> {
        Coordinate::nearest_lossy(x, y)
    }

    /// Round x, y float to nearest hex coordinates
    ///
    /// Return None, if exactly on the border of two hex coordinates
    pub fn nearest_lossy(x : f32, y : f32) -> Option<Coordinate<I>> {
        let z = 0f32 - x - y;

        let mut rx = x.round();
        let mut ry = y.round();
        let mut rz = z.round();

        let x_diff = (rx - x).abs();
        let y_diff = (ry - y).abs();
        let z_diff = (rz - z).abs();

        if x_diff > y_diff && x_diff > z_diff {
            rx = -ry - rz;
        } else if y_diff > z_diff {
            ry = -rx - rz;
        } else {
            rz = -rx - ry;
        }

        let x_diff = (rx - x).abs();
        let y_diff = (ry - y).abs();
        let z_diff = (rz - z).abs();

        if x_diff + y_diff + z_diff > 0.99 {
            return None;
        }

        Some(Coordinate {
            x: num::FromPrimitive::from_f32(rx).unwrap(),
            y: num::FromPrimitive::from_f32(ry).unwrap(),
        })
    }

    /// Old name for `nearest_with_offset`
    #[deprecated(note="use `nearest_with_offset` instead")]
    pub fn from_pixel_integer(spacing : IntegerSpacing<I>, v : (I, I)) -> (Coordinate<I>, (I, I)) {
        Coordinate::nearest_with_offset(spacing, v)
    }

    /// Find the hex containing a pixel. The origin of the pixel coordinates
    /// is the center of the hex at (0,0) in hex coordinates.
    pub fn from_pixel(x: f32, y: f32, spacing: Spacing) -> Coordinate<I> {
        match spacing {
            Spacing::PointyTop(size) => {
                let q = (x * 3f32.sqrt()/3f32 - y / 3f32) / size;
                let r = y * 2f32/3f32 / size;
                return Coordinate::nearest(q, -r -q);
            },
            Spacing::FlatTop(size) => {
                let q = x * 2f32/3f32 / size;
                let r = (-x / 3f32 + 3f32.sqrt()/3f32 * y) / size;
                return Coordinate::nearest(q, -r -q);
            }
        }
    }

    /// Convert integer pixel coordinates `v` using `spacing` to nearest coordinate that has both
    /// integer pixel coordinates lower or equal to `v`. Also return offset (in integer pixels)
    /// from that coordinate.
    ///
    /// Useful for ASCII visualization.
    // Took me a while to figure this out, but it seems to work. Brilliant.
    pub fn nearest_with_offset(spacing : IntegerSpacing<I>, v : (I, I)) -> (Coordinate<I>, (I, I)) {
        let (asc_x, asc_y) = v;

        let two : I = num::FromPrimitive::from_i8(2).unwrap();

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

        let coord = Coordinate{ x: q, y: -q - r };
        (coord, (qo, ro))
    }

    /// Old name for `to_pixel`
    #[deprecated(note="use `to_pixel` instead")]
    pub fn to_pixel_float(&self, spacing : Spacing) -> (f32, f32) {
        self.to_pixel(spacing)
    }

    /// Convert to pixel coordinates using `spacing`, where the
    /// parameter means the edge length of a hexagon.
    ///
    /// This function is meant for graphical user interfaces
    /// where resolution is big enough that floating point calculation
    /// make sense.
    pub fn to_pixel(&self, spacing : Spacing) -> (f32, f32) {
        let q = self.x.to_f32().unwrap();
        let r = self.z().to_f32().unwrap();
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
        let r = self.z();
        let two = num::FromPrimitive::from_i8(2).unwrap();

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

    /// Scale coordinate by a factor `s`
    pub fn scale(&self, s : I) -> Coordinate<I> {
        let x = self.x * s;
        let y = self.y * s;
        Coordinate{ x: x, y: y }
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

    /// Rotate self around a point `(0, 0, 0)` using angle of rotation `a`
    pub fn rotate_around_zero(&self, a : Angle) -> Coordinate<I> {

        let (x, y, z) = (self.x, self.y, self.z());

        let (x, y) = match a {
            Forward => (x, y),
            Right => (-z, -x),
            RightBack => (y, z),
            Back => (-x, -y),
            LeftBack => (z, x),
            Left => (-y, -z),
        };

        Coordinate{ x: x, y: y}
    }

    /// Rotate `self` around a `center` using angle of rotation `a`
    pub fn rotate_around(&self, center : Coordinate<I>, a : Angle) -> Coordinate<I> {
        let rel_p = *self - center;
        let rot_p = rel_p.rotate_around_zero(a);
        rot_p + center
    }

    /// Execute `f` for each coordinate in straight line from `self` to `dest`
    pub fn for_each_in_line_to<F>(&self, dest : Coordinate<I>, mut f : F)
        where
        F : FnMut(Coordinate<I>),
        for <'a> &'a I: Add<&'a I, Output = I>
        {
            if *self == dest {
                f(*self);
                return;
            }

            let n = self.distance(dest);

            let ax = self.x.to_f32().unwrap();
            let ay = self.y.to_f32().unwrap();
            let bx = dest.x.to_f32().unwrap();
            let by = dest.y.to_f32().unwrap();

            for i in range_inclusive(Zero::zero(), n) {
                let d = i.to_f32().unwrap() / n.to_f32().unwrap();
                let x = ax + (bx - ax) * d;
                let y = ay + (by - ay) * d;
                let c = Coordinate::nearest(x, y);
                f(c);
            }
    }

    /// Execute `f` for each coordinate in straight line from `self` to `dest`
    ///
    /// Skip points on the border of two tiles
    pub fn for_each_in_line_to_lossy<F>(&self, dest : Coordinate<I>, mut f : F)
        where
        F : FnMut(Coordinate<I>),
        for <'a> &'a I: Add<&'a I, Output = I>
        {
            if *self == dest {
                f(*self);
                return;
            }

            let n = self.distance(dest);

            let ax = self.x.to_f32().unwrap();
            let ay = self.y.to_f32().unwrap();
            let bx = dest.x.to_f32().unwrap();
            let by = dest.y.to_f32().unwrap();

            for i in range_inclusive(Zero::zero(), n) {
                let d = i.to_f32().unwrap() / n.to_f32().unwrap();
                let x = ax + (bx - ax) * d;
                let y = ay + (by - ay) * d;
                let c = Coordinate::nearest_lossy(x, y);
                if let Some(c) = c {
                    f(c);
                }
            }
    }

    /// Execute `f` for pairs of coordinates in straight line from `self` to `dest`
    ///
    /// On edge condition the pair contains different members, otherwise it's the same.
    pub fn for_each_in_line_to_with_edge_detection<F>(&self, dest : Coordinate<I>, mut f : F)
        where
        F : FnMut((Coordinate<I>, Coordinate<I>)),
        for <'a> &'a I: Add<&'a I, Output = I>
        {
            if *self == dest {
                f((*self, *self));
                return;
            }

            let n = self.distance(dest);

            let ax = self.x.to_f32().unwrap();
            let ay = self.y.to_f32().unwrap();
            let bx = dest.x.to_f32().unwrap();
            let by = dest.y.to_f32().unwrap();

            for i in range_inclusive(Zero::zero(), n) {
                let d = i.to_f32().unwrap() / n.to_f32().unwrap();
                let x = ax + (bx - ax) * d;
                let y = ay + (by - ay) * d;
                let c1 = Coordinate::nearest(x + 0.000001, y + 0.000001);
                let c2 = Coordinate::nearest(x - 0.000001, y - 0.000001);
                f((c1, c2));
            }
    }

    /// Construct a straight line to a `dest`
    pub fn line_to(&self, dest : Coordinate<I>) -> Vec<Coordinate<I>>
    where
        for <'a> &'a I: Add<&'a I, Output = I>
    {
        let mut res = Vec::new();

        self.for_each_in_line_to(dest, |c| {
            res.push(c);
        });

        res
    }

    /// Construct a straight line to a `dest`
    ///
    /// Skip points on the border of two tiles
    pub fn line_to_lossy(&self, dest : Coordinate<I>) -> Vec<Coordinate<I>>
    where
        for <'a> &'a I: Add<&'a I, Output = I>
    {
        let mut res = Vec::new();

        self.for_each_in_line_to_lossy(dest, |c| {
            res.push(c);
        });

        res
    }

    /// Construct a straight line to a `dest`
    pub fn line_to_with_edge_detection(&self, dest : Coordinate<I>) -> Vec<(Coordinate<I>, Coordinate<I>)>
    where
        for <'a> &'a I: Add<&'a I, Output = I>
    {
        let mut res = Vec::new();

        self.for_each_in_line_to_with_edge_detection(dest, |c| {
            res.push(c);
        });

        res
    }

    /// Z coordinate
    pub fn z(&self) -> I
    {
        -self.x - self.y
    }

    /// Direction from center `(0, 0)` to coordinate
    ///
    /// In case of diagonals (edge of two major directions), prefers direction that is clockwise
    /// from the diagonal
    ///
    /// Returns:
    /// None if is center
    ///
    /// ```
    /// use hex2d::{Direction, Coordinate};
    /// use hex2d::{Left, Right};
    ///
    /// let center = Coordinate::new(0, 0);
    ///
    /// assert_eq!(center.direction_from_center_cw(), None);
    ///
    /// for &d in Direction::all() {
    ///     assert_eq!((center + d).direction_from_center_cw(), Some(d));
    ///     assert_eq!((center + d + (d + Left)).direction_from_center_cw(), Some(d));
    ///     assert_eq!((center + d + (d + Right)).direction_from_center_cw(), Some(d + Right));
    /// }
    /// ```
    pub fn direction_from_center_cw(&self) -> Option<Direction> {

        let x = self.x;
        let y = self.y;
        let z = self.z();
        let zero : I = num::FromPrimitive::from_i8(0).unwrap();

        let xy = if z < zero { x >= y } else { x > y };
        let yz = if x < zero { y >= z } else { y > z };
        let zx = if y < zero { z >= x } else { z > x };
        match (xy, yz, zx) {
            (true, true, false) => Some(XZ),
            (true, false, false) => Some(XY),
            (true, false, true) => Some(ZY),

            (false, false, true) => Some(ZX),
            (false, true, true) => Some(YX),
            (false, true, false) => Some(YZ),
            (false, false, false) => None,
            (true, true, true) => panic!("You broke math"),
        }
    }

    /// Directions that lead from center to a given point.
    ///
    /// Returns an array of one or two directions.
    pub fn directions_from_center(&self) -> Vec<Direction> {
        let x = self.x;
        let y = self.y;
        let z = self.z();
        let zero : I = num::FromPrimitive::from_i8(0).unwrap();

        let mut dirs = Vec::with_capacity(2);

        if x > zero && z < zero {
            dirs.push(XZ)
        }

        if x > zero && y < zero {
            dirs.push(XY)
        }

        if z > zero && y < zero {
            dirs.push(ZY)
        }

        if z > zero && x < zero {
            dirs.push(ZX)
        }

        if y > zero && z < zero {
            dirs.push(YZ)
        }

        if y > zero && x < zero {
            dirs.push(YX)
        }

        dirs
    }

    /// Direction from center `(0, 0)` to coordinate
    ///
    /// In case of diagonals (edge of two major directions), prefers direction that is
    /// counter-clockwise from the diagonal.
    ///
    /// Returns:
    /// None if is center
    ///
    /// ```
    /// use hex2d::{Direction, Coordinate};
    /// use hex2d::{Left, Right};
    ///
    /// let center = Coordinate::new(0, 0);
    ///
    /// assert_eq!(center.direction_from_center_ccw(), None);
    ///
    /// for &d in Direction::all() {
    ///     assert_eq!((center + d).direction_from_center_ccw(), Some(d));
    ///     assert_eq!((center + d + (d + Left)).direction_from_center_ccw(), Some(d + Left));
    ///     assert_eq!((center + d + (d + Right)).direction_from_center_ccw(), Some(d));
    /// }
    /// ```
    pub fn direction_from_center_ccw(&self) -> Option<Direction> {

        let x = self.x;
        let y = self.y;
        let z = self.z();
        let zero : I = num::FromPrimitive::from_i8(0).unwrap();

        let xy = if z > zero { x >= y } else { x > y };
        let yz = if x > zero { y >= z } else { y > z };
        let zx = if y > zero { z >= x } else { z > x };
        match (xy, yz, zx) {
            (true, true, false) => Some(XZ),
            (true, false, false) => Some(XY),
            (true, false, true) => Some(ZY),

            (false, false, true) => Some(ZX),
            (false, true, true) => Some(YX),
            (false, true, false) => Some(YZ),
            (false, false, false) => None,
            (true, true, true) => panic!("You broke math"),
        }
    }

    /// Directions from self to `coord`
    pub fn directions_to(&self, coord : Coordinate<I>) -> Vec<Direction> {
        (coord - *self).directions_from_center()
    }

    /// Direction from self to `coord`
    ///
    /// In case of diagonals (edge of two major directions), prefers direction that is clockwise
    /// from the diagonal.
    ///
    /// Returns:
    /// None if is center
    pub fn direction_to_cw(&self, coor : Coordinate<I>) -> Option<Direction> {
        (coor - *self).direction_from_center_cw()
    }

    /// Direction from self to `coor`
    ///
    /// In case of diagonals (edge of two major directions), prefers direction that is
    /// counter-clockwise from the diagonal.
    ///
    /// Returns:
    /// None if is center
    pub fn direction_to_ccw(&self, coor: Coordinate<I>) -> Option<Direction> {
        (coor - *self).direction_from_center_ccw()
    }

    /// Distance between two Coordinates
    pub fn distance(&self, c : Coordinate<I>) -> I {
        ((self.x - c.x).abs() + (self.y - c.y).abs() + (self.z() - c.z()).abs())
            / num::FromPrimitive::from_i8(2).unwrap()
    }

    /// All coordinates in radius `r`
    pub fn range(&self, r : I) -> Vec<Coordinate<I>>
    where
        for <'a> &'a I: Add<&'a I, Output = I>
    {

        let rc = (if r < Zero::zero() { I::one()-r } else { r }).to_usize().unwrap();
        let mut res = Vec::with_capacity(3*(rc+rc*rc)+1);
        self.for_each_in_range(r, |c| res.push(c));

        res
    }

    /// Execute `f` for all coordinates in radius `r`
    pub fn for_each_in_range<F>(&self, r : I, mut f : F)
        where
        F : FnMut(Coordinate<I>),
        for <'a> &'a I: Add<&'a I, Output = I> {
        for x in range_inclusive(-r, r) {
            for y in range_inclusive(max(-r, -x-r), min(r, -x+r)) {
                f(Coordinate{
                    x: self.x + x,
                    y: self.y + y,
                });
            }
        }
    }

    /// A ring of radius `r`, starting in a corner in a given Direction
    ///
    /// Example: Elements in order for Ring of radius 2, Direction ZX, CCW
    ///
    /// ```norust
    ///              8
    ///            9   7
    ///         10   .   6
    ///            .   .
    ///         11   x   5
    ///            .   .
    ///          0   .   4
    ///            1   3
    ///              2
    /// ```
    ///
    /// ```
    ///
    /// use hex2d::{Coordinate, Spin, XY};
    ///
    /// let center = Coordinate::new(5, -1);
    ///
    /// for &c in &center.neighbors() {
    ///     for &ring_c in &c.ring(5, Spin::CCW(XY)) {
    ///         assert_eq!(c.distance(ring_c), 5);
    ///     }
    /// }
    /// ```
    pub fn ring(&self, r : i32, s : Spin) -> Vec<Coordinate<I>> {
        let mut res = Vec::with_capacity(if r == 0 { 1 } else if r < 0 { (r*-6) as usize } else { (r*6) as usize });
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
            num::FromPrimitive::from_i32(r).unwrap()
            );
        let mut cur_dir = start_dir + start_angle;

        for _ in 0..6 {
            let cur_dir_coord = cur_dir.to_coordinate();
            for _ in 0..r {
                f(cur_coord);
                cur_coord = cur_coord + cur_dir_coord;
            }
            cur_dir = cur_dir + step_angle;
        }
    }
}

impl<I : Integer> ToCoordinate<I> for Coordinate<I> {
    fn to_coordinate(&self) -> Coordinate<I> {
        *self
    }
}

impl<I : Integer> ToCoordinate<I> for (I, I) {
    fn to_coordinate(&self) -> Coordinate<I> {
        let (x, y) = *self;
        Coordinate::new(x, y)
    }
}

impl<I : Integer, T: ToCoordinate<I>> Add<T> for Coordinate<I> {
    type Output = Coordinate<I>;

    fn add(self, c : T) -> Coordinate<I> {
        let c = c.to_coordinate();

        Coordinate {
            x: self.x + c.x,
            y: self.y + c.y,
        }
    }
}

impl<I : Integer, T: ToCoordinate<I>> Sub<T> for Coordinate<I> {
    type Output = Coordinate<I>;

    fn sub(self, c : T) -> Coordinate<I> {
        let c = c.to_coordinate();

        Coordinate {
            x: self.x - c.x,
            y: self.y - c.y,
        }
    }
}

impl<I : Integer> Neg for Coordinate<I>
{
    type Output = Coordinate<I>;

    fn neg(self) -> Coordinate<I> {
        Coordinate { x: -self.x, y: -self.y }
    }
}

impl<I : Integer> Position<I>
{
    /// Create a new Position
    pub fn new(coord : Coordinate<I>, dir : Direction) -> Position<I> {
        Position{ coord: coord, dir: dir }
    }
}

impl<I : Integer> ToDirection for Position<I>
{
    fn to_direction(&self) -> Direction {
        self.dir
    }
}

impl<I : Integer> ToCoordinate<I> for Position<I>
{
    fn to_coordinate(&self) -> Coordinate<I> {
        self.coord
    }
}

impl<I : Integer> Add<Coordinate<I>> for Position<I> {
    type Output = Position<I>;

    fn add(self, c : Coordinate<I>) -> Position<I> {
        let c = c.to_coordinate();

        Position {
            coord: self.coord + c,
            dir: self.dir,
        }
    }
}

impl<I : Integer> Sub<Coordinate<I>> for Position<I>
{
    type Output = Position<I>;

    fn sub(self, c : Coordinate<I>) -> Position<I> {
        let c = c.to_coordinate();

        Position {
            coord: self.coord - c,
            dir: self.dir,
        }
    }
}

impl<I : Integer> Add<Angle> for Position<I> 
{
    type Output = Position<I>;

    fn add(self, a : Angle) -> Position<I> {
        Position {
            coord: self.coord,
            dir: self.dir + a,
        }
    }
}

impl Direction {
    /// Static array of all directions
    ///
    /// ```
    /// use hex2d::Direction;
    ///
    /// assert_eq!(Direction::all().len(), 6);
    /// ```
    pub fn all() -> &'static [Direction; 6] {
        &ALL_DIRECTIONS
    }

    /// Return a vector of an arc including Directions `steps` away from the original Direction both
    /// sides from left to right.
    ///
    /// ```
    /// use hex2d::{Direction};
    /// use hex2d::Angle::*;
    ///
    /// for &d in Direction::all() {
    ///     assert_eq!(d.arc(0), vec!(d));
    ///     assert_eq!(d.arc(1), vec!(d + Left, d, d + Right));
    ///     assert_eq!(d.arc(2), vec!(d + LeftBack, d + Left, d, d + Right, d + RightBack));
    ///     assert_eq!(d.arc(3), vec!(d + LeftBack, d + Left, d, d + Right, d + RightBack, d + Back));
    /// }
    /// ```
    pub fn arc(&self, steps : u8) -> Vec<Direction> {
        match steps {
            0 => vec!(*self),
            1 => vec!(*self + Left, *self, *self + Right),
            2 => vec!(*self + LeftBack, *self + Left, *self, *self + Right, *self + RightBack),
            _ => vec!(*self + LeftBack, *self + Left, *self, *self + Right, *self + RightBack, *self + Back),
        }
    }

    /// Create Direction from integer in [0, 6) range
    ///
    /// This should probably be internal
    pub fn from_int<I : Integer>(i : I) -> Direction {
        match i.mod_floor(&num::FromPrimitive::from_i8(6).unwrap()).to_u8().unwrap() {
            0 => YZ,
            1 => XZ,
            2 => XY,
            3 => ZY,
            4 => ZX,
            5 => YX,
            _ => panic!()
        }
    }

    /// Convert to integer in [0, 6) range
    ///
    /// This should probably be internal
    pub fn to_int<I : Integer>(&self) -> I {
       num::FromPrimitive::from_u8(*self as u8).unwrap()
    }

    /// Convert to angle for pointy-topped map, in radians, grows clockwise, 0.0 points up
    pub fn to_radians_pointy<T: Float>(&self) -> T {
        T::from(match *self {
            Direction::YZ => PI * (5.5 / 3.0),
            Direction::XZ => PI * (0.5 / 3.0),
            Direction::XY => PI * (1.5 / 3.0),
            Direction::ZY => PI * (2.5 / 3.0),
            Direction::ZX => PI * (3.5 / 3.0),
            Direction::YX => PI * (4.5 / 3.0),
        }).unwrap()
    }

    /// Convert to angle for flat-topped map, in radians, grows clockwise, 0.0 points up
    pub fn to_radians_flat<T: Float>(&self) -> T {
        self.to_radians_pointy::<T>() + T::from(PI * (0.5 / 3.0)).unwrap()
    }
}

impl ToDirection for Direction {
    fn to_direction(&self) -> Direction {
        *self
    }
}

impl<T: ToDirection> Sub<T> for Direction {
    type Output = Angle;

    fn sub(self, c : T) -> Angle {
        let c = c.to_direction();

        Angle::from_int::<i8>(self.to_int::<i8>() - c.to_int::<i8>())
    }
}

impl<I : Integer> ToCoordinate<I> for Direction {
    fn to_coordinate(&self) -> Coordinate<I> {
        let (x, y) = match *self {
            YZ => (0, 1),
            XZ => (1, 0),
            XY => (1, -1),
            ZY => (0, -1),
            ZX => (-1, 0),
            YX => (-1, 1),
        };

        Coordinate {
            x: num::FromPrimitive::from_i8(x).unwrap(),
            y: num::FromPrimitive::from_i8(y).unwrap(),
        }
    }
}

impl Neg for Direction {
    type Output = Direction ;

    fn neg(self) -> Direction {
        Direction::from_int::<i8>(self.to_direction().to_int::<i8>() + 3)
    }
}

impl Angle {
    /// Static array of all angles
    ///
    /// ```
    /// use hex2d::Angle;
    ///
    /// assert_eq!(Angle::all().len(), 6);
    /// ```
    pub fn all() -> &'static [Angle; 6] {
        &ALL_ANGLES
    }

    /// Create Angle from integer in [0, 6) range
    ///
    /// This should probably be internal
    pub fn from_int<I : Integer>(i : I) -> Angle {
        match i.mod_floor(&num::FromPrimitive::from_i8(6).unwrap()).to_u8().unwrap() {
            0 => Forward,
            1 => Right,
            2 => RightBack,
            3 => Back,
            4 => LeftBack,
            5 => Left,
            _ => panic!()
        }
    }

    /// Convert to integer in [0, 6) range
    ///
    /// This should probably be internal
    pub fn to_int<I : Integer>(&self) -> I {
       num::FromPrimitive::from_u8(*self as u8).unwrap()
    }
}

impl Add<Angle> for Direction {
    type Output = Direction;

    fn add(self, a : Angle) -> Direction {
        Direction::from_int(self.to_int::<i8>() + a.to_int::<i8>())
    }
}
