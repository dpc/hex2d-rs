// Copyright 2014 Dawid Ciężarkiewicz
// See LICENSE file for more information

use super::*;
use super::Spacing::*;

fn with_test_points<F : Fn(Coordinate) -> ()>(f : F) {
    let offs = [-2i32, -1, 0, 1, 2, 1000, -1000, 1001, -1001];
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

    with_test_points(|c : Coordinate| {
        for &sd in Direction::all() {
            let p = Position::new(c, sd);

            assert_eq!(p + Forward, p);
            assert_eq!(p + Right + Left, p);
            assert_eq!(p + Right + Right, p + RightBack);
            assert_eq!(p + Right + Right + Right, p + Back);
            assert_eq!(p + Left + Left, p + LeftBack);
            assert_eq!(p + Left + Left + Left, p + Back);
            assert_eq!(p + RightBack + RightBack + RightBack, p);
        }
    });
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
    with_test_points(|c : Coordinate| {
        assert_eq!(1, c.range(0).len());
        assert_eq!(7, c.range(1).len());
        assert_eq!(19, c.range(2).len());
        assert_eq!(37, c.range(3).len());
        assert_eq!((5 + 6 + 7 + 8 ) * 2 + 9, c.range(4).len());
    });
}

#[test]
fn range_distance() {
    with_test_points(|c : Coordinate| {
        for r in 0..10 {
            for p in c.range(r).iter() {
                assert!(p.distance(c) <= r);
            }
        }
    });
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
        assert_eq!(c.to_pixel_float(p_spacing), (0f32, 0f32));
        assert_eq!(c.to_pixel_float(f_spacing), (0f32, 0f32));
    }

    assert_eq!((2i32, -1i32).to_coordinate().to_pixel_float(f_spacing), (6f32, 0f32));
    assert_eq!((-2i32, 1i32).to_coordinate().to_pixel_float(f_spacing), (-6f32, 0f32));
    assert_eq!((1i32, 1i32).to_coordinate().to_pixel_float(p_spacing), (0f32, -6f32));
    assert_eq!((2i32, 2i32).to_coordinate().to_pixel_float(p_spacing), (0f32, -12f32));
}

#[test]
fn simple_from_pixel() {
    for &spacing in [
        IntegerSpacing::PointyTop(2, 1),
        IntegerSpacing::PointyTop(4, 6),
        IntegerSpacing::FlatTop(3, 2),
    ].iter() {
        with_test_points(|c : Coordinate| {
            let ascii_pix = c.to_pixel_integer(spacing);
            let (coord, pix_off) = Coordinate::from_pixel_integer(spacing, ascii_pix);
            assert_eq!((c, (0, 0)), (coord, pix_off));
        });
    }
}

#[test]
fn simple_rotations_around_zero() {
        with_test_points(|c : Coordinate| {
            assert_eq!(c, c.rotate_around_zero(Left).rotate_around_zero(Right));
            assert_eq!(c.rotate_around_zero(LeftBack),
            c.rotate_around_zero(Left).rotate_around_zero(Left));
            assert_eq!(c.rotate_around_zero(RightBack),
            c.rotate_around_zero(Right).rotate_around_zero(Right));
            assert_eq!(
                c.rotate_around_zero(Back),
                c.rotate_around_zero(Right)
                .rotate_around_zero(Right)
                .rotate_around_zero(Right)
            );
            assert_eq!(
                c.rotate_around_zero(Back),
                c.rotate_around_zero(Left)
                .rotate_around_zero(Left)
                .rotate_around_zero(Left)
            );
            assert_eq!(
                c.rotate_around_zero(Back),
                -c
                );
        });
}

#[test]
fn simple_rotations_around() {
        with_test_points(|c : Coordinate| {
            with_test_points(|p : Coordinate| {
                assert_eq!(p, p.rotate_around(c, Left).rotate_around(c, Right));
                assert_eq!(
                    p.rotate_around(c, LeftBack),
                    p.rotate_around(c, Left).rotate_around(c, Left)
                    );
                assert_eq!(
                    p.rotate_around(c, RightBack),
                    p.rotate_around(c, Right).rotate_around(c, Right)
                    );
                assert_eq!(
                    p.rotate_around(c, Back),
                    p.rotate_around(c, Right)
                    .rotate_around(c, Right)
                    .rotate_around(c, Right)
                    );
                assert_eq!(
                    p.rotate_around(c, Back),
                    p.rotate_around(c, Left)
                    .rotate_around(c, Left)
                    .rotate_around(c, Left)
                    );
            });
        });
}

#[test]
fn simple_direction_from_center() {

    let c = Coordinate::new(0, 0);

    assert_eq!(c.direction_from_center_cw(), None);
    assert_eq!(c.direction_from_center_ccw(), None);

    for &dir in Direction::all().iter() {
        assert_eq!((c + dir).direction_from_center_cw(), Some(dir));
        assert_eq!((c + dir).direction_from_center_ccw(), Some(dir));
        assert_eq!((c + dir + (dir + Left)).direction_from_center_cw(), Some(dir));
        assert_eq!((c + dir + (dir + Right)).direction_from_center_ccw(), Some(dir));
    }
}

#[test]
fn simple_direction_to() {

    with_test_points(|c : Coordinate| {
        assert_eq!(c.direction_to_cw(c), None);
        assert_eq!(c.direction_to_ccw(c), None);

        for &dir in Direction::all().iter() {
            assert_eq!(c.direction_to_cw(c + dir), Some(dir));
            assert_eq!(c.direction_to_ccw(c + dir), Some(dir));
            assert_eq!(c.direction_to_cw(c + dir + (dir + Left)), Some(dir));
            assert_eq!(c.direction_to_ccw(c + dir + (dir + Right)), Some(dir));
            assert_eq!(c.direction_to_cw(c + dir + (dir + Left) + dir + (dir + Left)), Some(dir));
            assert_eq!(c.direction_to_ccw(c + dir + (dir + Right) + dir + (dir + Right)), Some(dir));
        }
    });
}

#[test]
fn simple_direction_sub() {
    for &dir in Direction::all().iter() {
        for &angle in Angle::all().iter() {
            assert_eq!((dir + angle) - dir, angle);
        }
    }
}
#[test]
fn simple_line_to() {
    with_test_points(|c : Coordinate| {
        assert_eq!(c.line_to(c), vec!(c));
    });
}

