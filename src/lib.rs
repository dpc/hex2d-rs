// Copyright 2014 Dawid Ciężarkiewicz
// See LICENSE file for more information

#![crate_name = "hex2d"]
#![crate_type = "lib"]

#![warn(missing_docs)]
#![allow(unstable)]

//! Hexagonal map operations
//!
//! The coordinate system is supposed to be similar to the one used usually on screens,
//! which means y grows "downward" (well, southwest, really).
//!
//! ```notrust
//!     (0,0) ----> x
//!      /   /N \
//!     /  NW\__/NE
//!    /  \__/  \__
//!   /   /SW\__/SE
//!  v       /S \__
//! y
//! ```

extern crate num;
extern crate rand;

use num::Integer;
use std::num::{Int,UnsignedInt,SignedInt,ToPrimitive,FromPrimitive};
use std::fmt;
use std::ops::{Add, Neg, Sub};
use std::rand::Rand;

use AbsoluteDirection::{
    North,
    NorthEast,
    NorthWest,
    SouthEast,
    SouthWest,
    South,
};

use Direction::{
    Left, Right,
    Backward, Forward,
};

#[cfg(test)]
mod test;

/// Relative direction
#[derive(Copy)]
#[derive(Clone)]
#[derive(Show)]
#[derive(Eq)]
#[derive(PartialEq)]
pub enum Direction {
    /// Forward
    Forward,
    /// Backward
    Backward,
    /// Right-Forward
    Right,
    /// Left-Forward
    Left
}

/// Absolute direction
#[derive(Clone)]
#[derive(Copy)]
#[derive(Show)]
#[derive(Eq)]
#[derive(PartialEq)]
#[derive(FromPrimitive)]
pub enum AbsoluteDirection {
    /// Up
    North = 0,
    /// Up-Right
    NorthEast,
    /// Down-Right
    SouthEast,
    /// Down
    South,
    /// Down-Left
    SouthWest,
    /// Up -Left
    NorthWest
}

pub static ALL_DIRECTIONS: [AbsoluteDirection; 6] = [North, NorthEast, SouthEast, South, SouthWest, NorthWest];

/// Point on 2d hexagonal grid
#[derive(Clone)]
#[derive(Copy)]
#[derive(Eq)]
#[derive(PartialEq)]
pub struct Point<I : Int = i32> {
    /// `x` coordinate
    pub x : I,
    /// `y` coordinate
    pub y : I
}

/// Position on the hexagonal grid
///
/// `Point` + `AbsoluteDirection` it's heading.
#[derive(Clone)]
#[derive(Copy)]
#[derive(Eq)]
#[derive(PartialEq)]
pub struct Position<I : Int = i32> {
    /// Point on the grid
    pub p : Point<I>,
    /// Absolute direction
    pub dir : AbsoluteDirection
}

/// Map of `T`
pub struct Map<T, U : UnsignedInt = u32> {
    width : U,
    height : U,
    tiles : Vec<Vec<T>>
}

/// Can be treated as a `Point`
pub trait AsPoint<I : Int = i32> {
    /// Get the `Point` part of this data
    fn as_point<'a>(&'a self) -> &'a Point<I>;
}

/// Can be treated a `mut Point`
pub trait AsMutPoint<I : Int = i32> {
    /// Get the `mut Point` part of this data
    fn as_mut_point<'a>(&'a mut self) -> &'a mut Point<I>;
}

/// Can be treated a `AbsoluteDirection`
trait AsAbsoluteDirection {
    /// Get the `AbsoluteDirection` part of this data
    fn as_direction<'a>(&'a self) -> &'a AbsoluteDirection;
}

/// Can be treated a `mut AbsoluteDirection`
trait AsMutAbsoluteDirection {
    /// Get the `mut AbsoluteDirection` part of this data
    fn as_mut_direction<'a>(&'a mut self) -> &'a mut AbsoluteDirection;
}

/// Can be wrapped over `Map`
pub trait MapWrappable<U : UnsignedInt = u32> {
    type Output;

    /// Wrap around the map of a given `width` and `height`.
    fn wrap(self, width: U, height: U) -> Self::Output;
}

/// Can be added to a `Point<I>`
trait PointAddable<I : Int = i32> {
    /// Add to `p`
    fn add_to_point(self, p : Point<I>) -> Point<I>;
    /// Substrat from `p`
    fn sub_from_point(self, p : Point<I>) -> Point<I>;
}

/// Can be added to a `Position`
trait PositionAddable<I : Int = i32> {
    /// Add to `pos`
    fn add_to_position(self, pos : Position<I>) -> Position<I>;
}

/// Can be added to a `AbsoluteDirection`
trait AbsoluteDirectionAddable {
    /// Add to `dir`
    fn add_to_absolutedirection(self, dir : AbsoluteDirection) -> AbsoluteDirection;
}

/// Can be rotated by `AbsoluteDirection`
pub trait Rotatable {
    /// Add by `dir`, when `North` means 0 degrees
    fn rotate_by(self, dir : AbsoluteDirection) -> Self;
}

/// Can be translated
pub trait Translatable {
    /// Translate by `p`
    fn translate_by(self, p : Point) -> Self;
}

impl<I : Int> PositionAddable<I> for Direction {
    fn add_to_position(self, pos : Position<I>) -> Position<I> {
        match self {
            Right|Left =>
                Position {
                    p : pos.p,
                    dir : pos.dir + self
                },
                Forward|Backward =>
                    Position {
                        p : pos.p + (pos.dir + self),
                        dir: pos.dir
                    }
        }
    }
}

impl AbsoluteDirectionAddable for Direction {
    fn add_to_absolutedirection(self, p : AbsoluteDirection) -> AbsoluteDirection {
        p.turn(self)
    }
}

impl AbsoluteDirection {
    /// Create `AbsoluteDirection` from `u32` (0 to 5 range)
    pub fn from_u32(i : u32) -> AbsoluteDirection {
        match i {
            0 => North,
            1 => NorthEast,
            2 => SouthEast,
            3 => South,
            4 => SouthWest,
            5 => NorthWest,
            _ => panic!()
        }
    }

    /// Convert to u32
    pub fn to_u32(&self) -> u32 {
       *self as u32
    }

    /// Calculate `AbsoluteDirection` after rotating by `Direction`
    pub fn turn(&self, rd : Direction) -> AbsoluteDirection {
        AbsoluteDirection::from_u32(match rd {
            Forward =>   *self as u32,
            Backward => (*self as u32 + 3) % 6,
            Left =>     (*self as u32 + 5) % 6,
            Right =>    (*self as u32 + 1) % 6,
        })
    }

    fn turn_by_i32(&self, i : i32) -> AbsoluteDirection {
        AbsoluteDirection::from_u32(((*self as i32 + i) % 6) as u32)
    }

    fn turn_by(&self, dir : AbsoluteDirection) -> AbsoluteDirection {
        self.turn_by_i32(dir as i32)
    }

    /// Opposite direction
    ///
    /// Eg. `South` is an opposite direction to `North`
    pub fn opposite (&self) -> AbsoluteDirection {
        match *self {
            North => South,
            NorthEast => SouthWest,
            NorthWest => SouthEast,
            South => North,
            SouthEast => NorthWest,
            SouthWest => NorthEast,
        }
    }

    /// Negative `AbsoluteDirection` for turning operations
    ///
    /// For rotation operations `AbsoluteDirection` can be used as an angle value, with `North`
    /// considered 0 degrees. `opposite` is a direction that one would have to turn again, to get
    /// to original orientation.
    fn negative_rot(&self) -> AbsoluteDirection {
        match *self {
            North => North,
            NorthEast => NorthWest,
            NorthWest => NorthEast,
            South => South,
            SouthEast => SouthWest,
            SouthWest => SouthEast,
        }
    }

    /// Translate absolute Point i32o relative Point in relation to self.
    pub fn relative
        <T : Rotatable>
        (&self, d : T) -> T {
            d.rotate_by(self.negative_rot())
        }
}

impl AsAbsoluteDirection for AbsoluteDirection {
    fn as_direction<'a>(&'a self) -> &'a AbsoluteDirection {
        self
    }
}

impl<I : Int> PointAddable<I> for AbsoluteDirection {
    fn add_to_point(self, p : Point<I>) -> Point<I> {
        let one : I = Int::one();

        match self {
            North =>     Point { x: p.x, y: p.y - one },
            South =>     Point { x: p.x, y: p.y + one },
            SouthWest => Point { x: p.x - one, y: p.y + one},
            NorthEast => Point { x: p.x + one, y: p.y - one},
            NorthWest => Point { x: p.x - one, y: p.y},
            SouthEast => Point { x: p.x + one, y: p.y}
        }
    }

    fn sub_from_point(self, p : Point<I>) -> Point<I> {
        let one : I = Int::one();

        match self {
            North =>     Point { x: p.x, y: p.y + one },
            South =>     Point { x: p.x, y: p.y - one },
            SouthWest => Point { x: p.x + one, y: p.y - one},
            NorthEast => Point { x: p.x - one, y: p.y + one},
            NorthWest => Point { x: p.x + one, y: p.y},
            SouthEast => Point { x: p.x - one, y: p.y}
        }
    }
}

impl<T: AbsoluteDirectionAddable> Add<T> for AbsoluteDirection {
    type Output = AbsoluteDirection;

    fn add(self, p : T) -> AbsoluteDirection {
        p.add_to_absolutedirection(self)
    }
}

impl<I : SignedInt> Neg for Point<I> {
    type Output = Point<I>;

    fn neg(self) -> Point<I> {
        Point {x: -self.x, y: -self.y}
    }
}

impl<I : Int+Rand> rand::Rand for Point<I> {
    fn rand<R: rand::Rng>(rng: &mut R) -> Point<I> {
        Point {
            x: rng.gen::<I>(),
            y: rng.gen::<I>(),
        }
    }
}

impl Translatable for Point {
    fn translate_by(self, p : Point) -> Point {
        p + self
    }
}

impl Rotatable for Point {
    fn rotate_by(self, dir : AbsoluteDirection) -> Point {
        match *dir.as_direction() {
            North => Point {
                x: self.x,
                y: self.y
            },
            South => Point {
                x: - self.x,
                y: - self.y
            },
            NorthWest => Point {
                x: self.x + self.y,
                y: - self.x
            },
            SouthEast => Point {
                x: - self.x - self.y,
                y: self.x
            },
            NorthEast => Point {
                x: - self.y,
                y: self.x + self.y
            },
            SouthWest => Point {
                x: self.y,
                y: - self.x - self.y
            }
        }
    }
}

impl Rotatable for Position {
    fn rotate_by(self, dir : AbsoluteDirection) -> Position {
        Position {
            p: self.p.rotate_by(dir),
            dir: self.dir.rotate_by(dir),
        }
    }
}

impl Translatable for Position {
    fn translate_by(self, p : Point) -> Position {
        Position {
            p: self.p.translate_by(p),
            dir: self.dir,
        }
    }
}
impl rand::Rand for AbsoluteDirection {
    fn rand<R: rand::Rng>(rng: &mut R) ->  AbsoluteDirection {
        AbsoluteDirection::from_u32(rng.gen_range(0u32, 6))
    }
}

impl Rotatable for AbsoluteDirection {
    fn rotate_by(self, dir : AbsoluteDirection) -> AbsoluteDirection {
        self.turn_by(dir)
    }
}

impl Neg for AbsoluteDirection {
    type Output = AbsoluteDirection;

    fn neg(self) -> AbsoluteDirection {
        self + Backward
    }
}


impl<I : Int+ToPrimitive> Point<I> {
    /// Construct `Point` from `x` and `y` coordinates
    pub fn new(x : I, y : I) -> Point<I> {
        Point { x: x, y: y }
    }

    /// Is `pt` an neighbor?
    pub fn is_neighbor(&self, pt: Point<I>) -> bool {
        let sx : i64 = self.x.to_i64().unwrap();
        let sy : i64 = self.y.to_i64().unwrap();
        let px : i64 = pt.x.to_i64().unwrap();
        let py : i64 = pt.y.to_i64().unwrap();

        match (sx - px, sy - py) {
            (0, -1)  => true,
            (0, 1)   => true,
            (-1, 0)  => true,
            (1, 0)   => true,
            (-1, 1) => true,
            (1, -1)  => true,
            _ => {
                false
            }
        }
    }

    /// Offset between `self` and `p`
    pub fn offset(&self, p : Point<I>) -> Point<I> {
        p - *self
    }

    /// Translate `p` by `self`.
    pub fn translate(&self, p : Point<I>) -> Point<I> {
        *self + p
    }

    /// List of neighbors
    pub fn neighbors(&self) -> [Point<I>; 6] {
        let p = self;
        [*p + North, *p + NorthEast, *p + SouthEast,
        *p + South, *p + SouthWest, *p + NorthWest]
    }
}

impl<I : Int+ToPrimitive, U : UnsignedInt+FromPrimitive> MapWrappable<U> for Point<I> {
    type Output = Point<U>;

    /* TODO: Could this be done better? */
    fn wrap(self, w : U, h : U) -> Point<U> {
        let w_i64 : i64 = w.to_i64().unwrap();
        let h_i64 : i64 = h.to_i64().unwrap();
        let x_i64 : i64 = self.x.to_i64().unwrap();
        let y_i64 : i64 = self.x.to_i64().unwrap();
        let nx = x_i64.mod_floor(&w_i64);
        let ny = y_i64.mod_floor(&h_i64);
        let nx : U = FromPrimitive::from_i64(nx).unwrap();
        let ny : U = FromPrimitive::from_i64(ny).unwrap();

        Point { x: nx, y: ny}
    }
}

impl<T: PointAddable<I>, I : Int> Add<T> for Point<I> {
    type Output = Point<I>;

    fn add(self, p : T) -> Point<I> {
        p.add_to_point(self)
    }
}

impl<T: PointAddable<I>, I : Int> Sub<T> for Point<I> {
    type Output = Point<I>;

    fn sub(self, p : T) -> Point<I> {
        p.sub_from_point(self)
    }
}

impl<I : Int> PointAddable<I> for Point<I> {
    fn add_to_point(self, p : Point<I>) -> Point<I> {
        Point {x: self.x + p.x, y: self.y + p.y }
    }
    fn sub_from_point(self, p : Point<I>) -> Point<I> {
        Point {x: p.x - self.x, y: p.y - self.y }
    }
}

impl<I : Int> PositionAddable<I> for Point<I> {
    fn add_to_position(self, pos : Position<I>) -> Position<I> {
        Position {
            p : pos.p + self,
            dir : pos.dir
        }
    }
}

impl AsPoint for Point {
    fn as_point<'a>(&'a self) -> &'a Point {
        self
    }
}

impl AsMutPoint for Point {
    fn as_mut_point<'a>(&'a mut self) -> &'a mut Point {
        self
    }
}

impl fmt::Show for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "({}, {})", self.x, self.y)
    }
}

impl Position {
    /// Construct `Position` from `Point` and `AbsoluteDirection`
    pub fn new(p : Point, dir : AbsoluteDirection) -> Position {
        Position { p: p, dir: dir }
    }

    /// Construct `Position` from `x`, `y`, and `AbsoluteDirection`
    pub fn new2(x : i32, y : i32, dir : AbsoluteDirection) -> Position {
        Position { p : Point {x: x, y: y}, dir: dir }
    }

    /**
      Translate relative Point in relation to self i32o absolute Point.
     **/
    pub fn absolute
        <T : Rotatable+Translatable>
        (&self, p : T) -> T {
            p.rotate_by(self.dir).translate_by(self.p)
        }

    /// Translate absolute Point i32o relative Point in relation to self.
    pub fn relative
        <T : Rotatable+Translatable>
        (&self, p : T) -> T {
            p.translate_by(-self.p).rotate_by(self.dir.negative_rot())
        }

    /// Translate absolute Point i32o relative Point in relation to self
    /// taking i32o account that the pointers could have been wrapped by
    /// map size already.
    pub fn relative_wrapped
        <U, T : Rotatable+Translatable+AsMutPoint+AsPoint+Clone>
        (&self, map : &Map<U>, t : T) -> T
        {
            let p = t.as_point();
            let mut pos_x = self.p.x;
            let mut pos_y = self.p.y;
            let mut p_x = p.x;
            let mut p_y = p.y;
            let xdiff = (pos_x - p_x).abs();
            let ydiff = (pos_y - p_y).abs();

            if xdiff > map.width as i32 / 2 {
                if pos_x > p_x {
                    pos_x = pos_x - map.width as i32;
                } else {
                    p_x = p_x - map.width as i32;
                }
            }

            if ydiff > map.height as i32 / 2 {
                if pos_y > p_y {
                    pos_y = pos_y - map.height as i32;
                } else {
                    p_y = p_y - map.height as i32;
                }
            }

            let pos = Position::new(Point{x: pos_x, y: pos_y}, self.dir);
            let mut p = t.clone();
            p.as_mut_point().x = p_x;
            p.as_mut_point().y = p_y;

            pos.relative::<T>(p)
        }
}


impl<I : Int+ToPrimitive, U : UnsignedInt+FromPrimitive> MapWrappable<U> for Position<I> {
    type Output = Position<U>;

    fn wrap(self, w : U, h : U) -> Position<U> {
        Position{ dir: self.dir, p : self.p.wrap(w, h) }
    }
}

impl<T: PositionAddable> Add<T> for Position {
    type Output = Position;

    fn add(self, p : T) -> Position {
        p.add_to_position(self)
    }
}

impl fmt::Show for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "({:?}, {:?})", self.p, self.dir)
    }
}

impl rand::Rand for Position {
    fn rand<R: rand::Rng>(rng: &mut R) ->  Position {
        Position {
            dir: rng.gen::<AbsoluteDirection>(),
            p: rng.gen::<Point>(),
        }
    }
}


impl Neg for Position {
    type Output = Position;

    fn neg(self) -> Position {
        Position {
            p : self.p,
            dir : -self.dir
        }
    }
}

impl AsAbsoluteDirection for Position {
    fn as_direction<'a>(&'a self) -> &'a AbsoluteDirection {
        &self.dir
    }
}


impl AsPoint for Position {
    fn as_point<'a>(&'a self) -> &'a Point {
        &self.p
    }
}

impl AsMutAbsoluteDirection for Position {
    fn as_mut_direction<'a>(&'a mut self) -> &'a mut AbsoluteDirection {
        &mut self.dir
    }
}


impl AsMutPoint for Position {
    fn as_mut_point<'a>(&'a mut self) -> &'a mut Point {
        &mut self.p
    }
}

impl<T : Clone, U : UnsignedInt+ToPrimitive> Map<T, U> {
    /// Construct Map of given size, and filled with `fill`
    pub fn new(w: U, h: U, fill : T) -> Map<T, U> {
        Map {
            width: w,
            height: h,
            tiles: (0u64..w.to_u64().unwrap()).map(
                |_| (0u64..h.to_u64().unwrap()).map(|_| fill.clone()).collect()
                ).collect()
        }
    }

    /// Map `width`
    pub fn width(&self) -> U {
        self.width
    }

    /// Map `height`
    pub fn height(&self) -> U {
        self.width
    }

    /// Iterate over every `Point` of the `self`
    pub fn for_each_point<I : Int + FromPrimitive, F : Fn(Point<I>) -> ()>(&self, f : F) {
        for x in range(0u64, self.width().to_u64().unwrap()) {
            for y in range(0u64, self.height().to_u64().unwrap()) {
                let x : I = FromPrimitive::from_u64(x).unwrap();
                let y : I = FromPrimitive::from_u64(y).unwrap();
                let p : Point<I> = Point::new(x,y);
                f(p);
            }
        }
    }

    /// Clone map
    pub fn clone(&self, fill : T) -> Map<T, U> {
        Map::new(self.width, self.height, fill)
    }

    /// Access given map tile
    pub fn at<'a>(&'a self, p : Point) -> &'a T {
        &self.tiles[p.x as usize][p.y as usize]
    }

    /// Access given map tile (mutable)
    pub fn mut_at<'a>(&'a mut self, p : Point) -> &'a mut T {
        &mut self.tiles[p.x as usize][p.y as usize]
    }

    /// Wrap `p` over map size
    pub fn wrap<W:MapWrappable<U>>(&self, p : W) -> W::Output {
        p.wrap(self.width, self.height)
    }
}
