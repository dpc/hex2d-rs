extern crate hex2d;

use hex2d::{Point,Turn,Step};

fn main() {

    // Let's make a Point
    let p = Point::new(0, 0);
    println!("Center: \t{:?}", p);

    // Move it one tile North
    let p = p + hex2d::North;
    println!("One North:\t{:?}", p);

    // Make a position out of the Point, facing South
    let pos = p.to_position(hex2d::South);
    println!("Face South:\t{:?}", pos);

    // Turn Left:
    let pos = pos + Turn(hex2d::Left);
    println!("Turn Left:\t{:?}", pos);

    // Turn Backwards:
    let pos = pos + Turn(hex2d::Backward);
    println!("Turn Backward:\t{:?}", pos);

    // Step one tile Forward:
    let pos = pos + Step(hex2d::Forward);
    println!("Move Forward:\t{:?}", pos);
}
