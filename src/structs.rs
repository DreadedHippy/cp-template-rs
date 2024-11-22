
struct Coordinates(i32, i32);

impl Add for Coordinates {
    type Output = Coordinates;

    fn add(self, other: Coordinates) -> Coordinates {
        Coordinates(self.0 + other.0, self.1 + other.1)
    }
}

impl AddAssign for Coordinates {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
        self.1 += rhs.1;
    }
}

impl Coordinates {
    pub fn new() -> Self {
        Coordinates(0, 0)
    }

    pub fn from(raw: (i32, i32)) -> Self{
        Coordinates(raw.0, raw.1)
    }
}


fn evaluate(instruction : char) -> (i32, i32) {
	match instruction {
			'U' => {(0, 1)}
			'L' => {(-1, 0)}
			'D' => {(0, -1)}
			'R' => {(1, 0)},
			_ => {(0, 0)}
	}
}