//////////////////////////////////////////////////////////////////////////////////////////////////
// Lisp parser                                                                                  //
//                                                                                              //
// Write code that takes some Lisp code and returns an abstract syntax tree. The AST should     //
// represent the structure of the code and the meaning of each token. For example, if your code //
// is given "(first (list 1 (+ 2 3) 9))", it could return a nested array                        //
// like ["first", ["list", 1, ["+", 2, 3], 9]].                                                 //
//////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, PartialEq)]
enum Node {
    Integer(i64),
    Function(String),
}

fn some_chars<T, P, R>(predicate: P, reducer: R) -> impl Fn(&str) -> Result<(&str, T), &str>
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

fn new_integer(value: String) -> Node {
    Node::Integer(value.parse::<i64>().unwrap())
}

fn new_function(value: String) -> Node {
    Node::Function(value)
}

fn is_operator(value: char) -> bool {
    value == '+' || value == '-' || value == '*' || value == '/'
}

fn is_function_char(value: char) -> bool {
    value.is_alphabetic() || is_operator(value)
}

#[test]
fn test_parse_integer() {
    let parse_integer = some_chars(char::is_numeric, new_integer);
    assert_eq!(Ok(("", Node::Integer(1))), parse_integer("1"));
    assert_eq!(Ok(("", Node::Integer(2))), parse_integer("2"));
    assert_eq!(Ok(("", Node::Integer(123))), parse_integer("123"));
    assert_eq!(Err("apple"), parse_integer("apple"));
}

#[test]
fn test_parse_function() {
    let parse_function = some_chars(is_function_char, new_function);
    assert_eq!(
        Ok(("", Node::Function(String::from("apple")))),
        parse_function("apple")
    );
    assert_eq!(
        Ok(("", Node::Function(String::from("+")))),
        parse_function("+")
    );
    assert_eq!(Err("123"), parse_function("123"));
}
