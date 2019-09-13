//////////////////////////////////////////////////////////////////////////////////////////////////
// Lisp parser                                                                                  //
//                                                                                              //
// Write code that takes some Lisp code and returns an abstract syntax tree. The AST should     //
// represent the structure of the code and the meaning of each token. For example, if your code //
// is given "(first (list 1 (+ 2 3) 9))", it could return a nested array                        //
// like ["first", ["list", 1, ["+", 2, 3], 9]].                                                 //
//////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, PartialEq)]
enum Expression {
    Integer(i64),
    FunctionName(String),
    Symbol(char),
    FunctionCall(Box<(Expression, Vec<Expression>)>),
    Whitespace
}

// fn main() {
//     let parse_expression = or(vec![parse_integer, parse_function]);
//     let parse_function = match_pattern(vec![
//         literal(left_paren),
//         any_amount(whitespace()),
//         or(vec![identifier, operator]),
//         any_amount(whitespace()),
//         many(
//             whitespace_delimited(expression)
//         )
//        any_amount(whitespace()),
//        literal(right_paren),
//     ]);
// }

#[derive(Debug, Clone, PartialEq)]
enum OrResult<LT, RT, E> {
    LHS(LT),
    RHS(RT),
    Err(E),
}

fn or<L, R>(lhs_matcher: L, rhs_matcher: R) -> impl Fn(&str) -> Result<(&str, Expression), &str>
where
    L: Fn(&str) -> Result<(&str, Expression), &str>,
    R: Fn(&str) -> Result<(&str, Expression), &str>,
{
    move |input| match lhs_matcher(input) {
        Ok((rest, node)) => Ok((rest, node)),
        _ => match rhs_matcher(input) {
            Ok((rest, node)) => Ok((rest, node)),
            _ => Err(input),
        },
    }
}

fn followed_by<LT, RT, L, R>(
    lhs_matcher: L,
    rhs_matcher: R,
) -> impl Fn(&str) -> Result<((&str, (LT, RT))), &str>
where
    L: Fn(&str) -> Result<(&str, LT), &str>,
    R: Fn(&str) -> Result<(&str, RT), &str>,
{
    move |input| match lhs_matcher(input) {
        Ok((rest, lhs_node)) => match rhs_matcher(rest) {
            Ok((rest, rhs_node)) => Ok((rest, (lhs_node, rhs_node))),
            _ => Err(input),
        },
        _ => Err(input),
    }
}

fn match_some_chars<T, P, R>(predicate: P, reducer: R) -> impl Fn(&str) -> Result<(&str, T), &str>
where
    P: Fn(char) -> bool,
    R: Fn(String) -> T,
{
    move |input| {
        let mut matched = String::new();
        let mut chars = input.chars();

        match chars.next() {
            Some(next) if predicate(next) => matched.push(next),
            _ => return Err(input),
        }

        while let Some(next) = chars.next() {
            if predicate(next) {
                matched.push(next);
            } else {
                break;
            }
        }

        let next_index = matched.len();
        Ok((&input[next_index..], reducer(matched)))
    }
}

fn match_single_char<T, P, R>(predicate: P, reducer: R) -> impl Fn(&str) -> Result<(&str, T), &str>
where
    P: Fn(char) -> bool,
    R: Fn(char) -> T,
{
    move |input| match input.chars().next() {
        Some(next) if predicate(next) => Ok((&input[1..], reducer(next))),
        _ => return Err(input),
    }
}

fn new_integer(value: String) -> Expression {
    Expression::Integer(value.parse::<i64>().unwrap())
}

fn new_identifier(value: String) -> Expression {
    Expression::FunctionName(value)
}

fn new_operator(value: char) -> Expression {
    let mut string = String::new();
    string.push(value);
    Expression::FunctionName(string)
}

fn new_symbol(value: char) -> Expression {
    Expression::Symbol(value)
}

fn new_whitespace(_: String) -> Expression {
    Expression::Whitespace
}

fn is_operator(value: char) -> bool {
    value == '+' || value == '-' || value == '*' || value == '/'
}

fn is_symbol(value: char) -> bool {
    value == ')' || value == '('
}

#[test]
fn test_parse_integer() {
    let parse_integer = match_some_chars(char::is_numeric, new_integer);
    assert_eq!(Ok(("", Expression::Integer(1))), parse_integer("1"));
    assert_eq!(Ok(("", Expression::Integer(2))), parse_integer("2"));
    assert_eq!(Ok(("", Expression::Integer(123))), parse_integer("123"));
    assert_eq!(Err("apple"), parse_integer("apple"));
}

#[test]
fn test_parse_identifier() {
    let parse_identifier = match_some_chars(char::is_alphabetic, new_identifier);
    assert_eq!(
        Ok(("", Expression::FunctionName(String::from("apple")))),
        parse_identifier("apple")
    );
    assert_eq!(Err("+cool"), parse_identifier("+cool"));
    assert_eq!(Err("123"), parse_identifier("123"));
}

#[test]
fn test_parse_operator() {
    let parse_operator = match_single_char(is_operator, new_operator);
    assert_eq!(
        Ok(("", Expression::FunctionName(String::from("+")))),
        parse_operator("+")
    );
    assert_eq!(
        Ok(("", Expression::FunctionName(String::from("-")))),
        parse_operator("-")
    );
    assert_eq!(
        Ok(("cool", Expression::FunctionName(String::from("+")))),
        parse_operator("+cool")
    );
}

#[test]
fn test_parse_symbol() {
    let parse_symbol = match_single_char(is_symbol, new_symbol);
    assert_eq!(Ok(("", Expression::Symbol('('))), parse_symbol("("));
    assert_eq!(Ok(("", Expression::Symbol(')'))), parse_symbol(")"));
    assert_eq!(Err("+"), parse_symbol("+"));
}

#[test]
fn test_parse_function_name() {
    let parse_identifier = match_some_chars(char::is_alphabetic, new_identifier);
    let parse_operator = match_single_char(is_operator, new_operator);
    let parse_either = or(parse_identifier, parse_operator);
    assert_eq!(
        Ok(("", Expression::FunctionName(String::from("hello")))),
        parse_either("hello")
    );
    assert_eq!(
        Ok(("", Expression::FunctionName(String::from("+")))),
        parse_either("+")
    );
}

#[test]
fn test_parse_whitespace() {
    let parse_whitespace = match_some_chars(char::is_whitespace, new_whitespace);
    assert_eq!(
        Ok(("", Expression::Whitespace)),
        parse_whitespace(" ")
    );
}
