// Copyright 2014 Dawid Ciężarkiewicz
// See LICENSE file for more information

use super::Coordinate;
use super::Spin;

use super::Direction::*;
use super::Direction;
use super::Angle::*;
use super::Spacing::*;

use super::ToCoordinate;

fn with_test_points<F : Fn(Coordinate) -> ()>(f : F) {
    let offs = [-2, -1, 0, 1, 2, 1000];
    for &x in offs.iter() {
        for &y in offs.iter() {
            let p = Coordinate::new(x, y);
            f(p)
        }
    }
}

#[test]
fn coord_add_and_sub() {
    let a = Coordinate::new(-1, 2);
    let b = Coordinate::new(3, 4);
    let c = Coordinate::new(2, 6);

    assert_eq!(a + b, c);
    assert_eq!(c - b, a);
    assert_eq!(c - a, b);
}

#[test]
fn direction_add_and_sub() {
    for &d in Direction::all().iter() {
        assert_eq!(d + Forward, d);
        assert_eq!(d + Right + Left, d);
        assert_eq!(d + Right + Right, d + RightBack);
        assert_eq!(d + Right + Right + Right, d + Back);
        assert_eq!(d + Left + Left, d + LeftBack);
        assert_eq!(d + Left + Left + Left, d + Back);
        assert_eq!(d + RightBack + RightBack + RightBack, d);
    }
}


#[test]
fn coord_add_and_sub_direction() {
    with_test_points(|c : Coordinate| {
        assert_eq!(c + XY + YX, c);
        assert_eq!(c + ZY + YZ, c);
        assert_eq!(c + ZX + XZ, c);
        assert_eq!(c + ZX + YZ + XY, c);
        assert_eq!(c + XZ + ZY + YX, c);
    });
}

#[test]
fn coord_neighbors() {
    with_test_points(|c : Coordinate| {
        assert_eq!(c, c.neighbors().iter().fold(c, |sc, n| sc + (c - *n)));
    });
}

#[test]
fn move_circularly() {
    with_test_points(|p : Coordinate| {
        let mut start = p;
        let end = p;

        for &dir in Direction::all().iter() {
            start = start + dir;
        }

        assert_eq!(start, end);
    })
}

#[test]
fn move_circularly_double() {
    with_test_points(|p : Coordinate| {
        let mut start = p;
        let end = p;

        for &dir in Direction::all().iter() {
            start = start + dir + dir;
        }

        assert_eq!(start, end);
    });
}


#[test]
fn coord_range() {
    let c = Coordinate::new(0, 0);
    assert_eq!(1, c.range(0).len());
    assert_eq!(7, c.range(1).len());
    assert_eq!(19, c.range(2).len());
    assert_eq!(37, c.range(3).len());
    assert_eq!((5 + 6 + 7 + 8 ) * 2 + 9, c.range(4).len());
}

#[test]
fn range_distance() {
    let c = Coordinate::new(0, 0);
    for r in range(0, 10) {
        for p in c.range(r).iter() {
            assert!(p.distance(c) <= r);
        }
    }
}

#[test]
fn simple_rings() {
    with_test_points(|c : Coordinate| {
        for &d in Direction::all().iter() {
            {
                // CW r0
                let ring = c.ring(0, Spin::CW(d));

                assert_eq!(1, ring.len());
                assert_eq!(ring[0], c);
            }
            {
                // CCW r0
                let ring = c.ring(0, Spin::CCW(d));

                assert_eq!(1, ring.len());
                assert_eq!(ring[0], c);
            }
            {
                // CCW r1
                let ring = c.ring(1, Spin::CW(d));

                assert_eq!(6, ring.len());
                assert_eq!(ring[0], c + d);
                assert_eq!(ring[1], c + (d + Right));
                assert_eq!(ring[2], c + (d + RightBack));
                assert_eq!(ring[3], c + (d + Back));
                assert_eq!(ring[4], c + (d + LeftBack));
                assert_eq!(ring[5], c + (d + Left));
            }
            {
                // CCW r1
                let ring = c.ring(1, Spin::CCW(d));

                assert_eq!(6, ring.len());
                assert_eq!(ring[0], c + d);
                assert_eq!(ring[1], c + (d + Left));
                assert_eq!(ring[2], c + (d + LeftBack));
                assert_eq!(ring[3], c + (d + Back));
                assert_eq!(ring[4], c + (d + RightBack));
                assert_eq!(ring[5], c + (d + Right));
            }
            {
                // CW r2
                let ring = c.ring(2, Spin::CW(d));

                assert_eq!(12, ring.len());
                assert_eq!(ring[0], c + d + d);
                assert_eq!(ring[1], c + d + d + (d + RightBack));
                assert_eq!(ring[7], c - d - d - (d + RightBack));
                assert_eq!(ring[11], c + d + d + (d + LeftBack));
            }
            {
                // CCW r2
                let ring = c.ring(2, Spin::CCW(d));

                assert_eq!(12, ring.len());
                assert_eq!(ring[0], c + d + d);
                assert_eq!(ring[1], c + d + d + (d + LeftBack));
                assert_eq!(ring[7], c - d - d - (d + LeftBack));
                assert_eq!(ring[11], c + d + d + (d + RightBack));
            }
        }
    })
}

#[test]
fn simple_to_pixel() {

    let p_spacing = PointyTop(2f32);
    let f_spacing = FlatTop(2f32);

    {
        let c = Coordinate::new(0, 0);
        assert_eq!(c.to_pixel(p_spacing), (0f32, 0f32));
        assert_eq!(c.to_pixel(f_spacing), (0f32, 0f32));
    }

    assert_eq!((2i32, -1i32).to_coordinate().to_pixel(f_spacing), (6f32, 0f32));
    assert_eq!((-2i32, 1i32).to_coordinate().to_pixel(f_spacing), (-6f32, 0f32));
    assert_eq!((1i32, 1i32).to_coordinate().to_pixel(p_spacing), (0f32, -6f32));
    assert_eq!((2i32, 2i32).to_coordinate().to_pixel(p_spacing), (0f32, -12f32));
}
