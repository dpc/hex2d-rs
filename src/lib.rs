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
// Implement Eq between (i, i) and (i, i, i) by using Into<Coordinate>

#![crate_name = "hex2d"]
#![crate_type = "lib"]

#![warn(missing_docs)]

extern crate num;
#[cfg(feature="serde-serde")]
extern crate serde;
#[cfg(feature="serde-serde")]
#[macro_use]
extern crate serde_derive;

use num::{Float, One, Zero};
use std::ops::{Add, Sub, Neg};
use std::cmp::{max, min};
use std::convert::{Into, From, TryInto};
use std::f64::consts::PI;
use std::iter;

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
                    num::NumCast +
                    One + Zero + Copy { }

impl<I> Integer for I
where
I : num::Signed +
    num::Integer +
    num::CheckedAdd +
    num::ToPrimitive +
    num::FromPrimitive +
    num::NumCast +
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
    YZ,
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
    Forward,
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

impl From<Spin> for Direction {
    fn from(spin: Spin) -> Self {
        match spin {
            CW(d) => d,
            CCW(d) => d,
        }
    }
}

/// Floating point tile size for pixel conversion functions
#[derive(Copy, Clone, PartialEq, Debug, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
pub enum Spacing<F=f32> {
    /// Hex-grid with an edge on top
    FlatTop(F),
    /// Hex-grid with a corner on top
    PointyTop(F),
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

    /// Round x, y float to nearest hex coordinates
    pub fn nearest<F: Float>(x : F, y : F) -> Coordinate<I> {
        let zero: F = Zero::zero();
        let z: F = zero - x - y;

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
            x: I::from(rx).unwrap(),
            y: I::from(ry).unwrap(),
        }
    }

    /// Round x, y float to nearest hex coordinates
    ///
    /// Return None, if exactly on the border of two hex coordinates
    pub fn nearest_lossy<F: Float>(x : F, y : F) -> Option<Coordinate<I>> {
        let zero: F = Zero::zero();
        let z: F = zero - x - y;

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

        if x_diff + y_diff + z_diff > F::from(0.99).unwrap() {
            return None;
        }

        Some(Coordinate {
            x: I::from(rx).unwrap(),
            y: I::from(ry).unwrap(),
        })
    }

    /// Find the hex containing a pixel. The origin of the pixel coordinates
    /// is the center of the hex at (0,0) in hex coordinates.
    pub fn from_pixel<F: Float>(x: F, y: F, spacing: Spacing<F>) -> Coordinate<I> {
        let f3: F = F::from(3).unwrap();
        let f2: F = F::from(2).unwrap();
        let f3s: F = f3.sqrt();
        match spacing {
            Spacing::PointyTop(size) => {
                let q = (x * f3s/f3 - y / f3) / size;
                let r = y * f2/f3 / size;
                return Coordinate::nearest(q, -r -q);
            },
            Spacing::FlatTop(size) => {
                let q = x * f2/f3 / size;
                let r = (-x / f3 + f3s/f3 * y) / size;
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

    /// Convert to pixel coordinates using `spacing`, where the
    /// parameter means the edge length of a hexagon.
    ///
    /// This function is meant for graphical user interfaces
    /// where resolution is big enough that floating point calculation
    /// make sense.
    pub fn to_pixel<F: Float>(&self, spacing : Spacing<F>) -> (F, F) {
        let f3: F = F::from(3).unwrap();
        let f2: F = F::from(2).unwrap();
        let f3s: F = f3.sqrt();
        let q: F = F::from(self.x).unwrap();
        let r: F = F::from(self.z()).unwrap();
        match spacing {
            FlatTop(s) => (
                s * f3 / f2 * q,
                s * f3s * (r + q / f2)
                ),
            PointyTop(s) => (
                s * f3s * (q + r / f2),
                s * f3 / f2 * r
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

    fn line_to_iter_gen(&self, dest: Coordinate<I>) -> LineToGen<I> {
        let n = self.distance(dest);

        let ax = self.x.to_f32().unwrap();
        let ay = self.y.to_f32().unwrap();
        let bx = dest.x.to_f32().unwrap();
        let by = dest.y.to_f32().unwrap();
        LineToGen {
            n,
            ax,
            ay,
            bx,
            by,

            i: Zero::zero(),
        }
    }

    /// Iterator over each coordinate in straight line from `self` to `dest`
    pub fn line_to_iter(&self, dest: Coordinate<I>) -> LineTo<I> {
        LineTo(self.line_to_iter_gen(dest))
    }

    /// Iterator over each coordinate in straight line from `self` to `dest`
    ///
    /// Skip points on the border of two tiles
    pub fn line_to_lossy_iter(&self, dest: Coordinate<I>) -> LineToLossy<I> {
        LineToLossy(self.line_to_iter_gen(dest))
    }

    /// Iterator over each coordinate in straight line from `self` to `dest`
    ///
    /// On edge condition the pair contains different members, otherwise it's the same.
    pub fn line_to_with_edge_detection_iter(&self, dest: Coordinate<I>) -> LineToWithEdgeDetection<I> {
        LineToWithEdgeDetection(self.line_to_iter_gen(dest))
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

    /// An iterator over all coordinates in radius `r`
    pub fn range_iter(&self, r : I) -> Range<I> {
        Range{
            source: *self,
            x: -r,
            y: max(-r, -(-r)-r),
            r,
            counter: 0,
        }
    }

    /// Iterator over each coordinate in a ring
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
    ///     for ring_c in c.ring_iter(5, Spin::CCW(XY)) {
    ///         assert_eq!(c.distance(ring_c), 5);
    ///     }
    /// }
    /// ```
    pub fn ring_iter(&self, r : i32, s : Spin) -> Ring<I> {

        let (start_angle, step_angle, start_dir) = match s {
            CW(d) => (if r >= 0 { RightBack } else { Left }, Right, d),
            CCW(d) => (if r >= 0 { LeftBack } else { Right }, Left, d),
        };

        let cur_coord = *self + Coordinate::<I>::from(start_dir).scale(
            num::FromPrimitive::from_i32(r).unwrap()
        );
        let cur_dir = start_dir + start_angle;


        Ring {
            source: *self,
            cur_coord,
            cur_dir,
            step_angle,
            r: r.abs(),
            ii: 0,
            jj: 0,
            fuse: false,
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
/// Iterator over a ring
pub struct Ring<I: Integer> {
    source: Coordinate<I>,
    cur_coord: Coordinate<I>,
    cur_dir: Direction,
    step_angle: Angle,
    r: i32,
    ii: i32,
    jj: i32,
    fuse: bool,
}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    > Iterator for Ring<I>
{
    type Item = Coordinate<I>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.fuse {
            return None;
        }
        if self.r.is_zero() {
            self.fuse = true;
            return Some(self.source)
        }

        if self.jj >= self.r.abs() {
            self.ii += 1;
            if self.ii >= 6 {
                self.fuse = true;
                return None
            }
            self.cur_dir = self.cur_dir + self.step_angle;
            self.jj = 0;
        }
        self.jj += 1;

        let ret = Some(self.cur_coord);
        let cur_dir_coord: Coordinate<_> = self.cur_dir.into();
        self.cur_coord = self.cur_coord + cur_dir_coord;

        ret

    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.fuse {
            return (0, Some(0));
        }
        let total_size: usize = if self.r == 0 { 1 } else { (self.r*6) as usize };
        let past: usize = max(0, (self.jj+self.ii*self.r).try_into().unwrap());
        (total_size-past , Some(total_size-past))
    }
}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    > iter::FusedIterator for Ring<I> {}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    > iter::ExactSizeIterator for Ring<I> {}



#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
/// Iterator over an range
pub struct Range<I: Integer> {
    source: Coordinate<I>,
    x: I,
    y: I,
    r: I,
    counter: usize,
}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    > Iterator for Range<I>
{
    type Item = Coordinate<I>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.y > min(self.r, -self.x+self.r) {
            if self.x >= self.r {
                return None
            }
            self.x += One::one();
            self.y = max(-self.r, -self.x-self.r);
        }

        let ret = Some(Coordinate{
            x: self.source.x + self.x,
            y: self.source.y + self.y,
        });
        self.y += One::one();
        self.counter += 1;
        ret
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rc = (if self.r < Zero::zero() { I::one()-self.r } else { self.r }).to_usize().unwrap();
        let total_size = 3*(rc+rc*rc)+1;
        let current_size = total_size-self.counter;
        (current_size, Some(current_size))
    }
}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    > iter::FusedIterator for Range<I> {}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    >
    iter::ExactSizeIterator for Range<I>
{}


#[derive(Clone, PartialEq, Debug, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
/// Genertic iterator over a line return x, y values
struct LineToGen<I: Integer> {
    ax: f32,
    ay: f32,
    bx: f32,
    by: f32,
    n: I,
    i: I,
}

impl<
        I: num::Integer
            + num::Signed
            + std::marker::Copy
            + num::NumCast
            + num::FromPrimitive
            + num::ToPrimitive
            + num::CheckedAdd
            + std::marker::Copy
            + std::ops::AddAssign,
    > Iterator for LineToGen<I>
{
    type Item = (f32, f32);

    fn next(&mut self) -> Option<Self::Item> {
        if self.n == Zero::zero() {
            if self.i == Zero::zero() {
                self.i += One::one();
                return Some((self.ax, self.ay));
            } else {
                return None;
            }
        }

        if self.i > self.n {
            return None;
        }

        let d = self.i.to_f32().unwrap() / self.n.to_f32().unwrap();
        let x = self.ax + (self.bx - self.ax) * d;
        let y = self.ay + (self.by - self.ay) * d;
        self.i += One::one();
        Some((x, y))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let origin = Coordinate::<I>::nearest(self.ax, self.ay);
        let dest = Coordinate::nearest(self.bx, self.by);
        let total_size = origin.distance(dest) + One::one();
        let len = total_size-self.i;
        let len = len.to_usize().unwrap();
        (len, Some(len))
    }
}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    > iter::FusedIterator for LineToGen<I> {}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::ToPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    >
    iter::ExactSizeIterator for LineToGen<I>
{}

#[derive(Clone, PartialEq, Debug, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
/// An iterator over an a line of Coordinates
pub struct LineTo<I: Integer> (LineToGen<I>);

impl<
        I: num::Integer
            + num::Signed
            + std::marker::Copy
            + num::NumCast
            + num::FromPrimitive
            + num::ToPrimitive
            + num::CheckedAdd
            + std::marker::Copy
            + std::ops::AddAssign,
    > Iterator for LineTo<I>
{
    type Item = Coordinate<I>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(x, y)| Coordinate::nearest(x, y))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    > iter::FusedIterator for LineTo<I> {}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::ToPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    >
    iter::ExactSizeIterator for LineTo<I>
{}

#[derive(Clone, PartialEq, Debug, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
/// An iterator over an a line of Coordinates, using a lossy algorithm
pub struct LineToLossy<I: Integer> (LineToGen<I>);

impl<
        I: num::Integer
            + num::Signed
            + std::marker::Copy
            + num::NumCast
            + num::FromPrimitive
            + num::ToPrimitive
            + num::CheckedAdd
            + std::marker::Copy
            + std::ops::AddAssign,
    > Iterator for LineToLossy<I>
{
    type Item = Coordinate<I>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let c = self.0.next().map(|(x, y)| Coordinate::nearest_lossy(x, y));
            match c {
                Some(c@Some(_)) => return c,
                Some(None) => continue,
                None => return None,
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.0.size_hint().0/2, self.0.size_hint().1)
    }
}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    > iter::FusedIterator for LineToLossy<I> {}

#[derive(Clone, PartialEq, Debug, PartialOrd)]
#[cfg_attr(feature="serde-serde", derive(Serialize, Deserialize))]
/// An iterator over an a line of Coordinates, with edge detection
pub struct LineToWithEdgeDetection<I: Integer> (LineToGen<I>);

impl<
        I: num::Integer
            + num::Signed
            + std::marker::Copy
            + num::NumCast
            + num::FromPrimitive
            + num::ToPrimitive
            + num::CheckedAdd
            + std::marker::Copy
            + std::ops::AddAssign,
    > Iterator for LineToWithEdgeDetection<I>
{
    type Item = (Coordinate<I>, Coordinate<I>);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(x, y)| (
            Coordinate::nearest(x + 0.000001, y + 0.000001),
            Coordinate::nearest(x - 0.000001, y - 0.000001)
        ))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    > iter::FusedIterator for LineToWithEdgeDetection<I> {}

impl<
        I: num::Integer
        + num::Signed
        + std::marker::Copy
        + num::NumCast
        + num::FromPrimitive
        + num::ToPrimitive
        + num::CheckedAdd
        + std::marker::Copy
        + std::ops::AddAssign,
    >
    iter::ExactSizeIterator for LineToWithEdgeDetection<I>
{}

impl<I : Integer> From<(I, I)> for Coordinate<I> {
    fn from(xy: (I, I)) -> Self {
        let (x, y) = xy;
        Coordinate::new(x, y)
    }
}

impl<I : Integer, T: Into<Coordinate<I>>> Add<T> for Coordinate<I> {
    type Output = Coordinate<I>;

    fn add(self, c : T) -> Coordinate<I> {
        let c: Coordinate<_> = c.into();

        Coordinate {
            x: self.x + c.x,
            y: self.y + c.y,
        }
    }
}

impl<I : Integer, T: Into<Coordinate<I>>> Sub<T> for Coordinate<I> {
    type Output = Coordinate<I>;

    fn sub(self, c : T) -> Coordinate<I> {
        let c: Coordinate<_> = c.into();

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

impl<I : Integer> From<Position<I>> for Direction
{
    fn from(pos: Position<I>) -> Self {
        pos.dir
    }
}

impl<I : Integer> From<Position<I>> for Coordinate<I>
{
    fn from(pos: Position<I>) -> Self {
        pos.coord
    }
}

impl<I : Integer> Add<Coordinate<I>> for Position<I> {
    type Output = Position<I>;

    fn add(self, c : Coordinate<I>) -> Position<I> {
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

impl<T: Into<Direction>> Sub<T> for Direction {
    type Output = Angle;

    fn sub(self, c : T) -> Angle {
        let c: Direction = c.into();

        Angle::from_int::<i8>(self.to_int::<i8>() - c.to_int::<i8>())
    }
}

impl<I : Integer> From<Direction> for Coordinate<I> {
    fn from(dir: Direction) -> Self {
        let (x, y) = match dir {
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
        match self {
            YZ => ZY,
            XZ => ZX,
            XY => YX,
            ZY => YZ,
            ZX => XZ,
            YX => XY,
        }
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
