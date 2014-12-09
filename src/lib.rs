// Copyright 2014 Dawid Ciężarkiewicz
// See LICENSE file for more information

#![crate_name = "hex2d"]
#![crate_type = "lib"]

#![warn(missing_docs)]

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
use std::fmt;
use std::num::SignedInt;

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
#[deriving(Clone)]
#[deriving(Show)]
#[deriving(Eq)]
#[deriving(PartialEq)]
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
#[deriving(Clone)]
#[deriving(Show)]
#[deriving(Eq)]
#[deriving(PartialEq)]
#[deriving(FromPrimitive)]
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

pub static ALL_DIRECTIONS: [AbsoluteDirection, .. 6] = [North, NorthEast, SouthEast, South, SouthWest, NorthWest];


/// Point on 2d hexagonal grid
#[deriving(Clone)]
#[deriving(Eq)]
#[deriving(PartialEq)]
pub struct Point {
    /// `x` coordinate
    pub x : int,
    /// `y` coordingate
    pub y : int
}

/// Position on the hexagonal grid
///
/// `Point` + `AbsoluteDirection` it's heading.
#[deriving(Clone)]
#[deriving(Eq)]
#[deriving(PartialEq)]
pub struct Position {
    /// Point on the grid
    pub p : Point,
    /// Absolute direction
    pub dir : AbsoluteDirection
}

/// Map of `T`
pub struct Map<T> {
    width : uint,
    height : uint,
    tiles : Vec<Vec<T>>
}

/// Can be treated as a `Point`
pub trait AsPoint {
    /// Get the `Point` part of this data
    fn as_point<'a>(&'a self) -> &'a Point;
}

/// Can be treated a `mut Point`
pub trait AsMutPoint {
    /// Get the `mut Point` part of this data
    fn as_mut_point<'a>(&'a mut self) -> &'a mut Point;
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
pub trait MapWrappable<T> {
    /// Wrap around the map of a given `width` and `height`.
    fn wrap(&self, width: uint, height: uint) -> T;
}

/// Can be added to a `Point`
trait PointAddable {
    /// Add to `p`
    fn add_to_point(&self, p : &Point) -> Point;
    /// Substrat from `p`
    fn sub_from_point(&self, p : &Point) -> Point;
}

/// Can be added to a `Position`
trait PositionAddable {
    /// Add to `pos`
    fn add_to_position(&self, pos : &Position) -> Position;
}

/// Can be added to a `AbsoluteDirection`
trait AbsoluteDirectionAddable {
    /// Add to `dir`
    fn add_to_absolutedirection(&self, dir : &AbsoluteDirection) -> AbsoluteDirection;
}

/// Can be rotated by `AbsoluteDirection`
pub trait Rotatable {
    /// Add by `dir`, when `North` means 0 degrees
    fn rotate_by(&self, dir : AbsoluteDirection) -> Self;
}

/// Can be translated
pub trait Translatable {
    /// Translate by `p`
    fn translate_by(&self, p : Point) -> Self;
}

impl PositionAddable for Direction {
    fn add_to_position(&self, pos : &Position) -> Position {
        match *self {
            Right|Left =>
                Position {
                    p : pos.p,
                    dir : pos.dir + *self
                },
                Forward|Backward =>
                    Position {
                        p : pos.p + (pos.dir + *self),
                        dir: pos.dir
                    }
        }
    }
}

impl AbsoluteDirectionAddable for Direction {
    fn add_to_absolutedirection(&self, p : &AbsoluteDirection) -> AbsoluteDirection {
        p.turn(*self)
    }
}

impl AbsoluteDirection {
    /// Create `AbsoluteDirection` from `uint` (0 to 5 range)
    pub fn from_uint(i : uint) -> AbsoluteDirection {
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

    /// Convert to uint
    pub fn to_uint(&self) -> uint {
        FromPrimitive::from_int(*self as int).unwrap()
    }

    /// Calculate `AbsoluteDirection` after rotating by `Direction`
    pub fn turn(&self, rd : Direction) -> AbsoluteDirection {
        FromPrimitive::from_int(match rd {
            Forward => *self as int,
            Backward => (*self as int + 3) % 6,
            Left => (*self as int + 5) % 6,
            Right => (*self as int + 1) % 6,
        }).unwrap()
    }

    fn turn_by_int(&self, i : int) -> AbsoluteDirection {
        FromPrimitive::from_int((*self as int + i) % 6).unwrap()
    }

    fn turn_by(&self, dir : AbsoluteDirection) -> AbsoluteDirection {
        self.turn_by_int(dir as int)
    }

    /// Turn `AbsoluteDirection` into a relative `Point`
    /// (a `Point` that is result of moving in `AbsoluteDirection`
    /// starting from `(0, 0)`.
    pub fn to_relative_point(&self) -> Point {
        match *self {
            North =>     Point { x: 0, y: -1 },
            South =>     Point { x: 0, y: 1 },
            SouthWest => Point { x: -1, y: 1},
            NorthEast => Point { x: 1, y: -1},
            NorthWest => Point { x: -1, y: 0},
            SouthEast => Point { x: 1, y: 0}
        }
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
    /// For rotation operatins `AbsoluteDirection` can be used as an angle value, with `North`
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

    /// Translate absolute Point into relative Point in relation to self.
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

impl PointAddable for AbsoluteDirection {
    fn add_to_point(&self, p : &Point ) -> Point {
        *p + self.to_relative_point()
    }

    fn sub_from_point(&self, p : &Point) -> Point {
        let s = self.to_relative_point();
        Point {x: p.x - s.x, y: p.y - s.y }
    }
}

impl<T: AbsoluteDirectionAddable> Add<T, AbsoluteDirection> for AbsoluteDirection {
    fn add(&self, p : &T) -> AbsoluteDirection {
        p.add_to_absolutedirection(self)
    }
}

impl Neg<Point> for Point {
    fn neg(&self) -> Point {
        Point {x: -self.x, y: -self.y}
    }
}

impl rand::Rand for Point {
    fn rand<R: rand::Rng>(rng: &mut R) -> Point {
        Point {
            x: rng.gen::<int>(),
            y: rng.gen::<int>(),
        }
    }
}

impl Translatable for Point {
    fn translate_by(&self, p : Point) -> Point {
        p + *self
    }
}

impl Rotatable for Point {
    fn rotate_by(&self, dir : AbsoluteDirection) -> Point {
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
    fn rotate_by(&self, dir : AbsoluteDirection) -> Position {
        Position {
            p: self.p.rotate_by(dir),
            dir: self.dir.rotate_by(dir),
        }
    }
}

impl Translatable for Position {
    fn translate_by(&self, p : Point) -> Position {
        Position {
            p: self.p.translate_by(p),
            dir: self.dir,
        }
    }
}
impl rand::Rand for AbsoluteDirection {
    fn rand<R: rand::Rng>(rng: &mut R) ->  AbsoluteDirection {
        AbsoluteDirection::from_uint(rng.gen_range(0u, 6))
    }
}

impl Rotatable for AbsoluteDirection {
    fn rotate_by(&self, dir : AbsoluteDirection) -> AbsoluteDirection {
        self.turn_by(dir)
    }
}

impl Neg<AbsoluteDirection> for AbsoluteDirection {
    fn neg(&self) -> AbsoluteDirection {
        *self + Backward
    }
}


impl Point {
    /// Construct `Point` from `x` and `y` coordinates
    pub fn new(x : int, y : int) -> Point {
        Point { x: x, y: y }
    }

    /// Is `pt` an neighbor?
    pub fn is_neighbor(&self, pt: Point) -> bool {
        let r = *self - pt;
        match (r.x, r.y) {
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
    pub fn offset(&self, p : Point) -> Point{
        p - *self
    }

    /// Translate `p` by `self`.
    pub fn translate(&self, p : Point) -> Point {
        *self + p
    }

    /// List of neighbors
    pub fn neighbors(&self) -> [Point, ..6] {
        let p = self;
        [*p + North, *p + NorthEast, *p + SouthEast,
        *p + South, *p + SouthWest, *p + NorthWest]
    }
}

impl MapWrappable<Point> for Point {
    fn wrap(&self, w : uint, h : uint) -> Point {
        Point { x: self.x.mod_floor(&(w as int)), y: self.y.mod_floor(&(h as int))}
    }
}

impl<T: PointAddable> Add<T, Point> for Point {
    fn add(&self, p : &T) -> Point {
        p.add_to_point(self)
    }
}

impl<T: PointAddable> Sub<T, Point> for Point {
    fn sub(&self, p : &T) -> Point {
        p.sub_from_point(self)
    }
}

impl PointAddable for Point {
    fn add_to_point(&self, p : &Point) -> Point {
        Point {x: self.x + p.x, y: self.y + p.y }
    }
    fn sub_from_point(&self, p : &Point) -> Point {
        Point {x: p.x - self.x, y: p.y - self.y }
    }
}

impl PositionAddable for Point {
    fn add_to_position(&self, pos : &Position) -> Position {
        Position {
            p : pos.p + *self,
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
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}

impl Position {
    /// Construct `Position` from `Point` and `AbsoluteDirection`
    pub fn new(p : Point, dir : AbsoluteDirection) -> Position {
        Position { p: p, dir: dir }
    }

    /// Construct `Position` from `x`, `y`, and `AbsoluteDirection`
    pub fn new2(x : int, y : int, dir : AbsoluteDirection) -> Position {
        Position { p : Point {x: x, y: y}, dir: dir }
    }

    /**
      Translate relative Point in relation to self into absolute Point.
     **/
    pub fn absolute
        <T : Rotatable+Translatable>
        (&self, p : T) -> T {
            p.rotate_by(self.dir).translate_by(self.p)
        }

    /// Translate absolute Point into relative Point in relation to self.
    pub fn relative
        <T : Rotatable+Translatable>
        (&self, p : T) -> T {
            p.translate_by(-self.p).rotate_by(self.dir.negative_rot())
        }

    /// Translate absolute Point into relative Point in relation to self
    /// taking into account that the pointers could have been wrapped by
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

            if xdiff > map.width as int / 2 {
                if pos_x > p_x {
                    pos_x = pos_x - map.width as int;
                } else {
                    p_x = p_x - map.width as int;
                }
            }

            if ydiff > map.height as int / 2 {
                if pos_y > p_y {
                    pos_y = pos_y - map.height as int;
                } else {
                    p_y = p_y - map.height as int;
                }
            }

            let pos = Position::new(Point{x: pos_x, y: pos_y}, self.dir);
            let mut p = t.clone();
            p.as_mut_point().x = p_x;
            p.as_mut_point().y = p_y;

            pos.relative::<T>(p)
        }
}

impl MapWrappable<Position> for Position {
    fn wrap(&self, w : uint, h : uint) -> Position {
        Position{ dir: self.dir, p : self.p.wrap(w, h) }
    }
}

impl<T: PositionAddable> Add<T, Position> for Position {
    fn add(&self, p : &T) -> Position {
        p.add_to_position(self)
    }
}

impl fmt::Show for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}, {})", self.p, self.dir)
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


impl Neg<Position> for Position {
    fn neg(&self) -> Position {
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


impl<T : Clone> Map<T> {
    /// Construct Map of given size, and filled with `fill`
    pub fn new(w: uint, h: uint, fill : T) -> Map<T> {
        Map {
            width: w,
            height: h,
            tiles: Vec::from_fn(w, |_| Vec::from_fn(h, |_| fill.clone()))
        }
    }

    /// Map `width`
    pub fn width(&self) -> uint {
        self.width
    }

    /// Map `height`
    pub fn height(&self) -> uint {
        self.width
    }

    /// Iterate over every `Point` of the `self`
    pub fn for_each_point(&self, f : |Point|) {
        for x in range(0i, self.width() as int) {
            for y in range(0i, self.height() as int) {
                f(Point::new(x, y));
            }
        }
    }
}

impl<T> Map<T> {
    /// Clone map
    pub fn clone<F : Clone>(&self, fill : F) -> Map<F> {
        Map::new(self.width, self.height, fill)
    }

    /// Access given map tile
    pub fn at<'a>(&'a self, p : Point) -> &'a T {
        &self.tiles[p.x as uint][p.y as uint]
    }

    /// Access given map tile (mutable)
    pub fn mut_at<'a>(&'a mut self, p : Point) -> &'a mut T {
        &mut self.tiles[p.x as uint][p.y as uint]
    }

    /// Wrap `p` over map size
    pub fn wrap<T:MapWrappable<T>>(&self, p : T) -> T {
        p.wrap(self.width, self.height)
    }
}
