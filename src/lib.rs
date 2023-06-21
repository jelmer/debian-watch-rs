use num_derive::{FromPrimitive, ToPrimitive};
use num_traits::{FromPrimitive, ToPrimitive};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, FromPrimitive, ToPrimitive)]
#[allow(non_camel_case_types)]
#[repr(u16)]
enum SyntaxKind {
    L_PAREN = 0, // '('
    R_PAREN,     // ')'
    ATOM,        // '+', '15'
    WHITESPACE,  // whitespaces is explicit

    // composite nodes
    LIST, // `(+ 2 3)`
    ROOT, // top-level node: a list of s-expressions
}
use SyntaxKind::*;

// Convert to rowan's internal type from ours
impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        rowan::SyntaxKind(kind.to_u16().unwrap())
    }
}

// Boilerplate for the Language trait

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
enum Lang {}

impl rowan::Language for Lang {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        Self::Kind::from_u16(raw.0).unwrap()
    }

    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind.to_u16().unwrap())
    }
}

// Node type for the red tree
type SyntaxNode = rowan::SyntaxNode<Lang>;

// On to the parser

// We'll be buildling the nodes and tokens directly withought the builder api
use rowan::{GreenNode, GreenToken, NodeOrToken};

// The children type for a GreenNode is a `NodeOrToken`, which we need
// Might as well type alias
type Child = NodeOrToken<GreenNode, GreenToken>;

// Bring in the nom
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{multispace1, none_of},
    combinator::{all_consuming, map, opt, recognize},
    multi::{many0, many1},
    sequence::{pair, tuple},
};

// Setup the IResult type
type IResult<'a> = nom::IResult<&'a str, Child>;

// Convienence function for building the leaf nodes
fn leaf(kind: SyntaxKind, input: &str) -> Child {
    NodeOrToken::Token(GreenToken::new(kind.into(), input.into()))
}

// "Lexer"
fn lparen(input: &str) -> IResult {
    map(tag("("), |s| leaf(L_PAREN, s))(input)
}

fn rparen(input: &str) -> IResult {
    map(tag(")"), |s| leaf(R_PAREN, s))(input)
}

fn atom(input: &str) -> IResult {
    map(recognize(many1(none_of("() \t"))), |s| leaf(ATOM, s))(input)
}

fn whitespace(input: &str) -> IResult {
    map(multispace1, |s| leaf(WHITESPACE, s))(input)
}

// Parser
fn list(input: &str) -> IResult {
    map(
        tuple((
            lparen,
            opt(whitespace),
            opt(alt((list, atom))),
            many0(pair(whitespace, alt((list, atom)))),
            opt(whitespace),
            rparen,
        )),
        |(l, ws1, li1, body, ws2, r)| {
            let mut children: Vec<Child> = vec![l];
            if let Some(s) = ws1 {
                children.push(s)
            }
            if let Some(n) = li1 {
                children.push(n)
            }
            for (ws, elem) in body {
                children.push(ws);
                children.push(elem);
            }
            if let Some(s) = ws2 {
                children.push(s)
            }
            children.push(r);
            NodeOrToken::Node(GreenNode::new(LIST.into(), children))
        },
    )(input)
}

fn parse(input: &str) -> SyntaxNode {
    let body = all_consuming(list)(input).unwrap().1;
    let cst = GreenNode::new(ROOT.into(), [body]);
    SyntaxNode::new_root(cst)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let parsed = parse("(defn foo (x) (+ x x))");
        assert_eq!(
            r#"ROOT@[0; 22)
  LIST@[0; 22)
    L_PAREN@[0; 1) "("
    ATOM@[1; 5) "defn"
    WHITESPACE@[5; 6) " "
    ATOM@[6; 9) "foo"
    WHITESPACE@[9; 10) " "
    LIST@[10; 13)
      L_PAREN@[10; 11) "("
      ATOM@[11; 12) "x"
      R_PAREN@[12; 13) ")"
    WHITESPACE@[13; 14) " "
    LIST@[14; 21)
      L_PAREN@[14; 15) "("
      ATOM@[15; 16) "+"
      WHITESPACE@[16; 17) " "
      ATOM@[17; 18) "x"
      WHITESPACE@[18; 19) " "
      ATOM@[19; 20) "x"
      R_PAREN@[20; 21) ")"
    R_PAREN@[21; 22) ")"
"#,
            format!("{:#?}", parsed)
        )
    }
}
