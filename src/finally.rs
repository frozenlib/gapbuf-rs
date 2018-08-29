pub struct DropFn<F: FnOnce()>(Option<F>);
impl<F: FnOnce()> DropFn<F> {
    pub fn new(f: F) -> DropFn<F> {
        DropFn(Some(f))
    }
}
impl<F: FnOnce()> Drop for DropFn<F> {
    fn drop(&mut self) {
        use std::mem;
        if let Some(f) = mem::replace(&mut self.0, None) {
            f();
        }
    }
}

macro_rules! try_finally {
    ($try: block, $finally: block) => {
        {
            let _drop = $crate::finally::DropFn::new(|| { $finally });
            $try
        }
    };

    ($try: block, $finally: block, $($next_finally: block),+ ) => {
        {
            try_finally!{ {try_finally!($try,$finally)} , $( { $next_finally } ),+ }
        }
    };

    ($($e: expr),+) => {
        try_finally! { $({$e}),+ }
    };
}
