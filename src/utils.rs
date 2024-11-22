use std::collections::HashSet;


fn get_factors(num: usize) -> Vec<i64>{
	let root = f64::sqrt(num as f64) as i64 + 1;

	let mut result = HashSet::with_capacity(root as usize);

	for i in 1..=root {
			if num % i as usize == 0 {
					result.insert(i);
					result.insert(num as i64/i);
			}
			// println!("{:?}",result);
	}

	let r = result.into_iter().collect();
	r

}


fn format_radix(mut x: u32, radix: u32) -> String {
	let mut result = vec![];

	loop {
			let m = x % radix;
			x = x / radix;


			// will panic if you use a bad radix (< 2 or > 36).
			result.push(std::char::from_digit(m, radix).unwrap());
			if x == 0 {
					break;
			}
	}
	result.into_iter().rev().collect()
}


fn sort_vecdeque<T: Ord>(x: &mut VecDeque<T>) {
	x.rotate_right(x.as_slices().1.len());
	assert!(x.as_slices().1.is_empty());
	x.as_mut_slices().0.sort();
}


pub fn get_msb(n: u32) -> u32{
	32 - (n.leading_zeros() - 1)
}

//! BINARY SEARCH

fn binary_search() {	
	let (a, b) = (info[0], info[1]);
	
	let d = b-a;
	
	// let lim = 2*d;
	
	let (mut l, mut r) = (0, d);
	
	let mut mid = (r - l)/2;

	while l <= r {
		let calc = (mid*(mid+1))/2;

		if calc > d {
			r = mid -1;
		} else if calc < d {
			l = mid +1;
		} else {
			break
		}
			
			
		mid = (r+l)/2;
	}
		
	println!("{}", mid + 1);
		
}
pub struct SegmentTree {
	pub start: usize,
	pub end: usize,
	pub sum: i32,
	pub left: Option<Box<SegmentTree>>,
	pub right: Option<Box<SegmentTree>>
}

impl SegmentTree {
	pub fn new(start: usize, end: usize, vals: &[i32]) -> Self {
			if start == end {
					return Self {start, end, sum: vals[start], left: None, right: None}
			}


			let mid = start + (end-start) / 2;
			let left = Self::new(start, mid, vals);
			let right = Self::new(mid+1, end, vals);
			let sum = left.sum + right.sum;


			Self {
					start,
					end,
					sum,
					left: Some(Box::new(left)),
					right: Some(Box::new(right)),
			}
	}

	pub fn update(&mut self, index: usize, val: i32) {
			// Note: If leaf, update self
			if self.start == self.end && self.end == index {
					self.sum = val;
					return;
			}

			let mid = (self.end + self.start)/2;

			if index <= mid {
					self.left.as_mut().unwrap().update(index, val);
			} else {
					self.right.as_mut().unwrap().update(index, val);
			}

			self.sum = self.left.as_ref().unwrap().sum + self.right.as_ref().unwrap().sum
	}

	pub fn query(&self, start: usize, end: usize) -> i32{
			// Note: If leaf, update self
			if self.start == start && self.end == end {
					return self.sum ;
			}

			let mid = (self.end + self.start)/2;

			if end <= mid {
					return self.left.as_ref().unwrap().query(start, end);
			} else if start > mid {
					return self.right.as_ref().unwrap().query(start, end);
			} else {
					return self.left.as_ref().unwrap().query(start, mid)
							+ self.right.as_ref().unwrap().query(mid + 1, end);
			}
	}
}
