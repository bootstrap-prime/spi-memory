#![allow(unused_macros)]

#[cfg(feature = "log")]
macro_rules! error {
    ($($t:tt)*) => {{ defmt::error!($($t)*); }};
}

#[cfg(feature = "log")]
macro_rules! warn {
    ($($t:tt)*) => {{ defmt::warn!($($t)*); }};
}

#[cfg(feature = "log")]
macro_rules! info {
    ($($t:tt)*) => {{ defmt::info!($($t)*); }};
}

#[cfg(feature = "log")]
macro_rules! debug {
    ($($t:tt)*) => {{ defmt::debug!($($t)*); }};
}

#[cfg(feature = "log")]
macro_rules! trace {
    ($($t:tt)*) => {{ defmt::trace!($($t)*); }};
}

#[cfg(not(feature = "log"))]
macro_rules! error {
    ($($t:tt)*) => {{ format_args!($($t)*); }};
}

#[cfg(not(feature = "log"))]
macro_rules! warn {
    ($($t:tt)*) => {{ format_args!($($t)*); }};
}

#[cfg(not(feature = "log"))]
macro_rules! info {
    ($($t:tt)*) => {{ format_args!($($t)*); }};
}

#[cfg(not(feature = "log"))]
macro_rules! debug {
    ($($t:tt)*) => {{ format_args!($($t)*); }};
}

#[cfg(not(feature = "log"))]
macro_rules! trace {
    ($($t:tt)*) => {{ format_args!($($t)*); }};
}
