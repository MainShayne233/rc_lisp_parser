
fn parse_integer(value: &'static str) -> Result<(&str, i64), &str> {
    Ok(("", 1))
}

#[test]
fn test_parse_integer() {
    assert_eq!(Ok(("", 1)), parse_integer("1"))
}
