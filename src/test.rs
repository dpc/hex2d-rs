// Copyright 2014 Dawid Ciężarkiewicz
// See LICENSE file for more information
use super::Point;
use super::Position;
use super::ALL_DIRECTIONS;
use super::Direction::{Forward,Backward,Left,Right};
use super::AbsoluteDirection::{North,South,NorthWest,NorthEast,SouthWest,SouthEast};

fn with_test_points(f : |p : Point|) {
    let offs = [-2, -1, 0, 1, 2];
    for &x in offs.iter() {
        for &y in offs.iter() {
            let p = Point::new(x, y);
            f(p)
        }
    }
}

#[test]
fn point_add_and_sub() {
    let a = Point::new(-1, 2);
    let b = Point::new(3, 4);
    let c = Point::new(2, 6);

    assert_eq!(a + b, c);
    assert_eq!(c - b, a);
    assert_eq!(c - a, b);
}

#[test]
fn left_and_right() {
    let dirs = [North, NorthEast, SouthEast, South, SouthWest, NorthWest];

    for (i, &d) in dirs.iter().enumerate() {

        assert_eq!(d + Left, dirs[(i + 5) % 6]);
        assert_eq!(d + Right, dirs[(i + 1) % 6]);
    }
}

#[test]
fn direction_turn() {
    for &dir in ALL_DIRECTIONS.iter() {
        assert_eq!(dir.turn(Forward), dir);
        assert_eq!(dir.turn(Backward).turn(Backward), dir);
        assert_eq!(dir.turn(Left).turn(Right), dir);
        assert_eq!(dir.turn(Right).turn(Left),dir);
        assert_eq!(dir.turn(Left).turn(Left).turn(Left), dir.turn(Backward));
        assert_eq!(dir.turn(Right).turn(Right).turn(Right), dir.turn(Backward));
    }
}

#[test]
fn direction_turn_by_add() {
    for &dir in ALL_DIRECTIONS.iter() {
        assert_eq!(dir + Forward, dir);
        assert_eq!(dir + Backward + Backward, dir);
        assert_eq!(dir + Left + Right, dir);
        assert_eq!(dir + Right + Left, dir);
        assert_eq!(dir + Left + Left + Left, dir + Backward);
        assert_eq!(dir + Right + Right + Right, dir + Backward);
    }
}

#[test]
fn move_circularly() {
    with_test_points(|p : Point| {
        let mut start = p;
        let end = p;

        for &dir in ALL_DIRECTIONS.iter() {
            start = start + dir;
        }

        assert_eq!(start, end);
    })
}

#[test]
fn move_circularly_double() {
    with_test_points(|p : Point| {
        let mut start = p;
        let end = p;

        for &dir in ALL_DIRECTIONS.iter() {
            start = start + dir + dir;
        }

        assert_eq!(start, end);
    });
}

#[test]
fn position_make_circle() {
    with_test_points(|p : Point| {
        let start_p = p;
        for &start_dir in ALL_DIRECTIONS.iter() {
            for &side in [Left, Right].iter() {
                for &front_or_back in [Forward, Backward].iter() {
                    let mut pos = Position::new(start_p, start_dir);

                    for _ in ALL_DIRECTIONS.iter() {
                        pos = pos + front_or_back + side;
                    }

                    assert_eq!(pos, Position::new(start_p, start_dir));
                }
            }
        }

    });
}

#[test]
fn next_step_must_be_neighbour() {
    with_test_points(|p : Point| {
        for &dir in ALL_DIRECTIONS.iter() {
            assert!(p.is_neighbor(p + dir));
        }
    });
}

#[test]
fn next_two_steps_some_should_be_neighbour() {
    with_test_points(|p : Point| {
        for &dir in ALL_DIRECTIONS.iter() {
            assert!(!p.is_neighbor(p + dir + (dir + Left)));
            assert!(!p.is_neighbor(p + dir + (dir + Forward)));
            assert!(!p.is_neighbor(p + dir + (dir + Right)));
            assert!(p.is_neighbor(p + dir + (dir + Right + Right)));
            assert!(p.is_neighbor(p + dir + (dir + Left + Left)));
        }
    });
}

#[test]
fn point_is_not_its_own_neighbor() {
    with_test_points(|p : Point| {
        assert!(!p.is_neighbor(p));
    });
}

#[test]
fn position_absolute() {
    let zero = Point::new(0,0);
    with_test_points(|p : Point| {
        for &pos_dir in ALL_DIRECTIONS.iter() {
            let pos = Position::new(p, pos_dir);
            assert_eq!(pos.absolute(zero), p);
            for &side in [Right,Left,Forward].iter() {
                let mut zero_dir = North;
                let mut pos_dir = pos_dir;
                for _ in range(0u, 6) {
                    zero_dir = zero_dir + side;
                    pos_dir = pos_dir + side;
                }
                let mut zero_p = zero;
                let mut pos_p = pos.p;

                for _ in range(0u, 5) {
                    zero_p = zero_p + zero_dir;
                    pos_p = pos_p + pos_dir;
                }
                assert_eq!(pos.absolute(zero_p), pos_p);
            }
        }
    });
}
#[test]
fn relative_absolute() {

    with_test_points(|p : Point| {
        for &pos_dir in ALL_DIRECTIONS.iter() {
            let pos = Position {p: p, dir: pos_dir};
            with_test_points(|rp : Point| {
                assert_eq!(pos.absolute(pos.relative(rp)), rp);
                assert_eq!(pos.relative(pos.absolute(rp)), rp);
            })
        }
    });
}
