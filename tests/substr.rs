#![allow(
    // need to test cloning, these are deliberate.
    clippy::redundant_clone,
    // yep, we create owned instance just for comparison, to test comparison
    // with owned instacnces.
    clippy::cmp_owned,
    // Deliberate
    clippy::redundant_slicing,
)]
#![cfg(feature = "substr")]
use rcstr::{RcStr, Substr};

#[test]
fn double_substr() {
    let s: Substr = rcstr::literal!("foobarbaz").substr(3..);
    assert_eq!(s.as_str(), "barbaz");
    assert_eq!(s.substr(1..5), "arba");
    assert_eq!(s.substr(..5), "barba");
    assert_eq!(s.substr(1..), "arbaz");
    assert_eq!(s.substr(..), "barbaz");
    assert_eq!(s.substr(1..=4), "arba");
    assert_eq!(s.substr(..=4), "barba");
    assert_eq!(s.substr(1..=5), "arbaz");
    assert_eq!(s.substr(..=5), "barbaz");
    assert_eq!(
        s.substr((core::ops::Bound::Excluded(1), core::ops::Bound::Unbounded)),
        "rbaz"
    );
}

#[test]
fn single_substr() {
    let s = RcStr::from("barbaz");
    assert_eq!(s.substr(1..5), "arba");
    assert_eq!(s.substr(..5), "barba");
    assert_eq!(s.substr(1..), "arbaz");
    assert_eq!(s.substr(..), "barbaz");
    assert_eq!(s.substr(1..=4), "arba");
    assert_eq!(s.substr(..=4), "barba");
    assert_eq!(s.substr(1..=5), "arbaz");
    assert_eq!(s.substr(..=5), "barbaz");
    assert_eq!(
        s.substr((core::ops::Bound::Excluded(1), core::ops::Bound::Unbounded)),
        "rbaz"
    );
}

#[test]
fn substr_index() {
    let s = RcStr::from("_barbaz_").substr(1..7);
    assert_eq!(&s[1..5], "arba");
    assert_eq!(&s[..5], "barba");
    assert_eq!(&s[1..], "arbaz");
    assert_eq!(&s[..], "barbaz");
    assert_eq!(&s[1..=4], "arba");
    assert_eq!(&s[..=4], "barba");
    assert_eq!(&s[1..=5], "arbaz");
    assert_eq!(&s[..=5], "barbaz");
}

#[test]
#[should_panic]
fn substr_panic() {
    let s = RcStr::from("abc");
    let _v = &s[1..4];
}
#[test]
#[should_panic]
fn substr_panic1() {
    let s = RcStr::from("abc").substr(..2);
    let _v = &s.substr(1..3);
}
#[test]
#[should_panic]
fn substr_panic2() {
    let s = RcStr::from("🙀");
    let _v = &s.substr(1..);
}
#[test]
#[should_panic]
fn substr_panic3() {
    let s = RcStr::from(" 🙀").substr(1..);
    let _v = &s.substr(1..);
}
#[test]
#[should_panic]
fn substr_panic4() {
    let s = RcStr::from("abc").substr(..);
    let _v = &s.substr(1..4);
}

#[test]
fn test_various_partial_eq() {
    macro_rules! check_partial_eq {
        (@eq1; $a:expr, $b:expr) => {{
            // Note: intentionally not assert_eq.
            assert!($a == $b);
            assert!(!($a != $b));
            assert!($b == $a);
            assert!(!($b != $a));
        }};
        (@ne1; $a:expr, $b:expr) => {
            assert!($a != $b);
            assert!(!($a == $b));
            assert!($b != $a);
            assert!(!($b == $a));
        };
        (@eq; $a:expr, $b:expr) => {{
            check_partial_eq!(@eq1; $a, $b);
            check_partial_eq!(@eq1; $a.clone(), $b);
            check_partial_eq!(@eq1; $a.clone(), $a);
        }};
        (@ne; $a:expr, $b:expr) => {{
            check_partial_eq!(@ne1; $a, $b);
            check_partial_eq!(@ne1; $a.clone(), $b);
        }};
    }
    // really lazy to reuse Arcstr checks here..

    // could just use Substr::from but lets make sure we have substrs that are
    // nontrivial
    fn substr(s: &str) -> Substr {
        RcStr::from(format!("xx{}xx", s)).substr(2..s.len() + 2)
    }
    check_partial_eq!(@eq; substr("123"), "123");
    check_partial_eq!(@eq; substr("foobar"), *"foobar");
    check_partial_eq!(@eq; substr("🏳️‍🌈"), String::from("🏳️‍🌈"));
    check_partial_eq!(@eq; substr("🏳️‍⚧️"), std::borrow::Cow::Borrowed("🏳️‍⚧️"));
    check_partial_eq!(@eq; substr("🏴‍☠️"), std::borrow::Cow::Owned("🏴‍☠️".into()));
    check_partial_eq!(@eq; substr(":o"), std::rc::Rc::<str>::from(":o"));
    check_partial_eq!(@eq; substr("!!!"), std::sync::Arc::<str>::from("!!!"));
    check_partial_eq!(@eq; substr("examples"), RcStr::from("examples"));

    check_partial_eq!(@eq; substr(""), "");
    check_partial_eq!(@eq; substr(""), RcStr::from("abc").substr(3..));
    let twin = substr("1 2 3");
    let twin2 = twin.clone();
    check_partial_eq!(@eq; twin, twin2);

    check_partial_eq!(@ne; substr("123"), "124");
    check_partial_eq!(@ne; substr("Foobar"), *"FoobarFoobar");

    check_partial_eq!(@ne; substr("①"), String::from("1"));
    check_partial_eq!(@ne; substr(""), String::from("1"));
    check_partial_eq!(@ne; substr("abc"), String::from(""));

    check_partial_eq!(@ne; substr("butts"), std::borrow::Cow::Borrowed("boots"));
    check_partial_eq!(@ne; substr("bots"), std::borrow::Cow::Owned("🤖".into()));
    check_partial_eq!(@ne; substr("put"), std::rc::Rc::<str>::from("⛳️"));
    check_partial_eq!(@ne; substr("pots"), std::sync::Arc::<str>::from("🍲"));
    check_partial_eq!(@ne; substr("lots"), RcStr::from("auctions"));
}

#[test]
fn test_fmt() {
    assert_eq!(format!("{}", RcStr::from("__test__").substr(2..6)), "test");
    assert_eq!(
        format!("{:?}", RcStr::from("__test__").substr(2..6)),
        "\"test\""
    );
    assert_eq!(rcstr::format!("{:?}", "__test__"), "\"__test__\"");
    assert_eq!(rcstr::format!("test2"), "test2");
}
#[test]
fn test_parts_shallow_eq() {
    let parent = RcStr::from("12345");
    let sub = parent.substr(1..);
    assert!(RcStr::ptr_eq(&parent, sub.parent()));
    assert_eq!(sub.range(), 1..5);
    assert!(Substr::shallow_eq(&sub.clone(), &sub));
    assert!(Substr::shallow_eq(&sub.clone(), &parent.substr(1..)));
    assert!(Substr::shallow_eq(&sub, &parent.clone().substr(1..)));
    assert!(Substr::shallow_eq(&sub, &parent.substr(1..5)));
    assert!(!Substr::shallow_eq(&sub, &RcStr::from("12345").substr(1..)));
    assert!(!Substr::shallow_eq(&sub, &parent.substr(1..3)));
    assert!(!Substr::shallow_eq(&sub, &parent.substr(2..)));
    assert!(!Substr::shallow_eq(&sub, &parent.substr(..5)));
}

#[test]
fn test_ord() {
    let mut arr = [
        RcStr::from("_foo").substr(1..),
        RcStr::from("AAAbar").substr(3..),
        RcStr::from("zzzbaz").substr(3..),
    ];
    arr.sort();
    assert_eq!(&arr, &["bar", "baz", "foo"]);
}

#[test]
fn test_btreemap() {
    let mut m = std::collections::BTreeMap::new();

    for i in 0..100 {
        let prev = m.insert(RcStr::from(format!("key {}", i)).substr(1..), i);
        assert_eq!(prev, None);
    }

    for i in 0..100 {
        let s = format!("ey {}", i);
        assert_eq!(m.remove(s.as_str()), Some(i));
    }
}
#[test]
fn test_hashmap() {
    let mut m = std::collections::HashMap::new();
    for i in 0..100 {
        let prev = m.insert(RcStr::from(format!("key {}", i)).substr(1..), i);
        assert_eq!(prev, None);
    }
    for i in 0..100 {
        let key = format!("ey {}", i);
        let search = key.as_str();
        assert_eq!(m[search], i);
        assert_eq!(m.remove(search), Some(i));
    }
}

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    use serde_test::{assert_de_tokens, assert_tokens, Token};
    let teststr = RcStr::from("  test test 123 456").substr(2..);
    assert_tokens(&teststr, &[Token::BorrowedStr("test test 123 456")]);
    assert_tokens(&teststr.clone(), &[Token::BorrowedStr("test test 123 456")]);
    assert_tokens(&RcStr::default(), &[Token::BorrowedStr("")]);

    let checks = &[
        [Token::Str("123")],
        [Token::BorrowedStr("123")],
        [Token::String("123")],
        [Token::Bytes(b"123")],
        [Token::BorrowedBytes(b"123")],
        [Token::ByteBuf(b"123")],
    ];
    for check in checks {
        eprintln!("checking {:?}", check);
        assert_de_tokens(&Substr::from("123"), check);
    }
}

#[test]
fn test_loose_ends() {
    assert_eq!(Substr::default(), "");
    assert_eq!("abc".parse::<Substr>().unwrap(), "abc");
    let abc_sub = Substr::from(" abc ").substr(1..4);
    let abc_str: &str = abc_sub.as_ref();
    let abc_bytes: &[u8] = abc_sub.as_ref();
    assert_eq!(abc_str, "abc");
    assert_eq!(abc_bytes, b"abc");
    let full_src = RcStr::from("123");
    let sub = Substr::full(full_src.clone());
    assert!(RcStr::ptr_eq(&full_src, sub.parent()));
    assert_eq!(sub.range(), 0..3);
    let sub2 = Substr::from(&full_src);
    assert!(Substr::shallow_eq(&sub2, &sub));
}

#[test]
fn test_cow() {
    use std::borrow::Cow::{self, Borrowed, Owned};
    let cow: Cow<'_, str> = Borrowed("abcd");
    assert_eq!(Substr::from(cow), "abcd");

    let cow: Cow<'_, str> = Owned("abcd".into());
    assert_eq!(Substr::from(cow), "abcd");
    let sub = RcStr::from("XXasdfYY").substr(2..6);
    let cow: Option<Cow<'_, str>> = Some(&sub).map(Cow::from);
    assert_eq!(cow.as_deref(), Some("asdf"));

    let cow: Option<Cow<'_, str>> = Some(sub).map(Cow::from);
    assert!(matches!(cow, Some(Cow::Owned(_))));
    assert_eq!(cow.as_deref(), Some("asdf"));

    let st = { rcstr::literal!("_static should borrow_") };
    let ss = st.substr(1..st.len() - 1);
    {
        let cow: Option<Cow<'_, str>> = Some(ss.clone()).map(Cow::from);
        assert!(matches!(cow, Some(Cow::Borrowed(_))));
        assert_eq!(cow.as_deref(), Some("static should borrow"));
    }
    // works with any lifetime
    {
        let cow: Option<Cow<'static, str>> = Some(ss.clone()).map(Cow::from);
        assert!(matches!(cow, Some(Cow::Borrowed(_))));
        assert_eq!(cow.as_deref(), Some("static should borrow"));
    }
}

#[test]
fn test_inherent_overrides() {
    let s = RcStr::from("  abc ").substr(2..5);
    assert_eq!(s.as_str(), "abc");
    // let a = RcStr::from("foo");
    assert_eq!(s.len(), 3);
    assert!(!s.is_empty());
    assert!(s.substr(3..).is_empty());
    assert_eq!(s.to_string(), "abc");
}

#[test]
fn test_substr_from() {
    let a = RcStr::from("  abcdefg  ");
    let ss = a.substr_from(&a.as_str()[2..]);
    assert_eq!(ss, "abcdefg  ");
    assert!(Substr::shallow_eq(&ss, &a.substr(2..)));

    let ss = a.substr_from(&a.as_str()[..9]);
    assert_eq!(ss, "  abcdefg");
    assert!(Substr::shallow_eq(&ss, &a.substr(..9)));

    let ss = a.substr_from(a.trim());
    assert_eq!(ss, "abcdefg");
    assert!(Substr::shallow_eq(&ss, &a.substr(2..9)));
}

#[test]
fn test_try_substr_from_using() {
    let orig = rcstr::literal!("   bcdef   ");
    let a = orig.substr(1..10);
    let ss = a.try_substr_from(&a.as_str()[1..8]).unwrap();
    assert_eq!(ss, " bcdef ");
    assert!(Substr::shallow_eq(&ss, &orig.substr(2..9)));
    let ss2 = orig.try_substr_using(str::trim);
    assert_eq!(ss2.unwrap(), "bcdef");

    let nil = orig.try_substr_using(|s| s.get(5..100).unwrap_or(""));
    assert_eq!(nil.unwrap(), "");
    let nil = a.try_substr_using(|s| s.get(5..100).unwrap_or(""));
    assert_eq!(nil.unwrap(), "");
    // lifetimes make it pretty hard to misuse this — I do wonder if generative
    // lifetimes would make it even harder... But for now, we keep the checks.
    let outside = a.try_substr_using(|_| &RcStr::as_static(&orig).unwrap()[..]);
    assert_eq!(outside, None);
    let outside_l = a.try_substr_using(|_| &RcStr::as_static(&orig).unwrap()[1..]);
    assert_eq!(outside_l, None);
    let outside_r = a.try_substr_using(|_| &RcStr::as_static(&orig).unwrap()[..10]);
    assert_eq!(outside_r, None);
    let outside_lr = a.try_substr_using(|_| &RcStr::as_static(&orig).unwrap()[1..10]);
    assert_eq!(outside_lr.as_deref(), Some("  bcdef  "));
}
#[test]
#[should_panic]
fn test_substr_using_panic0() {
    let orig = rcstr::literal!("   bcdef   ");
    let a = orig.substr(1..10);
    let _s = a.substr_using(|_| &RcStr::as_static(&orig).unwrap()[..]);
}
#[test]
#[should_panic]
fn test_substr_using_panic1() {
    let orig = rcstr::literal!("   bcdef   ");
    let a = orig.substr(1..10);
    let _s = a.substr_using(|_| &RcStr::as_static(&orig).unwrap()[1..]);
}

#[test]
#[should_panic]
fn test_substr_using_panic2() {
    let orig = rcstr::literal!("   bcdef   ");
    let a = orig.substr(1..10);
    let _s = a.substr_using(|_| &RcStr::as_static(&orig).unwrap()[..10]);
}

#[test]
fn test_substr_from_using() {
    let orig = RcStr::from("   bcdef   ");
    let a = orig.substr(1..10);
    let ss = a.substr_from(&a.as_str()[1..8]);
    assert_eq!(ss, " bcdef ");
    assert!(Substr::shallow_eq(&ss, &orig.substr(2..9)));
    let ss2 = orig.substr_using(str::trim);
    assert_eq!(ss2, "bcdef");

    let nil = orig.substr_using(|s| s.get(5..100).unwrap_or(""));
    assert_eq!(nil, "");
    let nil = a.substr_using(|s| s.get(5..100).unwrap_or(""));
    assert_eq!(nil, "");
}

#[test]
#[should_panic]
fn test_substr_from_panic() {
    let a = RcStr::from("  abcdefg  ");
    let _s = a.substr_from("abcdefg");
}

#[test]
#[should_panic]
fn test_substr_using_arc_panic() {
    let a = RcStr::from("  abcdefg  ");
    let _s = a.substr_using(|_| "abcdefg");
}

#[test]
fn test_try_substr_from() {
    let a = RcStr::from("  abcdefg  ");
    assert!(a.try_substr_from("abcdefg").is_none());
    let ss = a.try_substr_from(&a.as_str()[2..]);
    assert_eq!(ss.as_deref(), Some("abcdefg  "));
    assert!(Substr::shallow_eq(&ss.unwrap(), &a.substr(2..)));

    let ss = a.try_substr_from(&a.as_str()[..9]);
    assert_eq!(ss.as_deref(), Some("  abcdefg"));
    assert!(Substr::shallow_eq(&ss.unwrap(), &a.substr(..9)));

    let ss = a.try_substr_from(a.trim());
    assert_eq!(ss.as_deref(), Some("abcdefg"));
    assert!(Substr::shallow_eq(&ss.unwrap(), &a.substr(2..9)));
}

#[test]
fn test_try_substr_from_substr() {
    let subs = rcstr::literal_substr!("  abcdefg  ");
    assert!(subs.try_substr_from("abcdefg").is_none());
    let ss = subs.try_substr_from(&subs.as_str()[2..]);
    assert_eq!(ss.as_deref(), Some("abcdefg  "));
    assert!(Substr::shallow_eq(&ss.unwrap(), &subs.substr(2..)));

    let ss = subs.try_substr_from(&subs.as_str()[..9]);
    assert_eq!(ss.as_deref(), Some("  abcdefg"));
    assert!(Substr::shallow_eq(&ss.unwrap(), &subs.substr(..9)));

    let ss = subs.try_substr_from(subs.trim());
    assert_eq!(ss.as_deref(), Some("abcdefg"));
    assert!(Substr::shallow_eq(&ss.unwrap(), &subs.substr(2..9)));
}
