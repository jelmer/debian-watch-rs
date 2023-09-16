use crate::SyntaxKind;
use crate::SyntaxKind::*;

/// Split the input string into a flat list of tokens
fn lex(text: &str) -> Vec<(SyntaxKind, String)> {
    fn tok(t: SyntaxKind) -> m_lexer::TokenKind {
        let sk = rowan::SyntaxKind(t as u16);
        m_lexer::TokenKind(sk.0)
    }
    fn kind(t: m_lexer::TokenKind) -> SyntaxKind {
        match t.0 {
            0 => KEY,
            1 => VALUE,
            2 => EQUALS,
            3 => CONTINUATION,
            4 => NEWLINE,
            5 => WHITESPACE,
            6 => ERROR,
            _ => unreachable!(),
        }
    }

    let lexer = m_lexer::LexerBuilder::new()
        .error_token(tok(ERROR))
        .tokens(&[
            (tok(KEY), r"[a-z]+"),
            (tok(VALUE), r"[^\s=]*[^\s=\\]"),
            (tok(CONTINUATION), r"\\\n"),
            (tok(EQUALS), r"="),
            (tok(NEWLINE), r"\n"),
            (tok(WHITESPACE), r"\s+"),
        ])
        .build();

    lexer
        .tokenize(text)
        .into_iter()
        .map(|t| (t.len, kind(t.kind)))
        .scan(0usize, |start_offset, (len, kind)| {
            let s: String = text[*start_offset..*start_offset + len].into();
            *start_offset += len;
            Some((kind, s))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::SyntaxKind::*;
    pub static WATCHV1: &str = r#"version=4
opts=filenamemangle=s/.+\/v?(\d\S+)\.tar\.gz/syncthing-gtk-$1\.tar\.gz/ \
  https://github.com/syncthing/syncthing-gtk/tags .*/v?(\d\S+)\.tar\.gz
"#;

    #[test]
    fn test_empty() {
        assert_eq!(super::lex(""), vec![]);
    }

    #[test]
    fn test_simple() {
        assert_eq!(
            super::lex(WATCHV1),
            vec![
                (KEY, "version".into()),
                (EQUALS, "=".into()),
                (VALUE, "4".into()),
                (NEWLINE, "\n".into()),
                (KEY, "opts".into()),
                (EQUALS, "=".into()),
                (KEY, "filenamemangle".into()),
                (EQUALS, "=".into()),
                (
                    VALUE,
                    "s/.+\\/v?(\\d\\S+)\\.tar\\.gz/syncthing-gtk-$1\\.tar\\.gz/".into()
                ),
                (WHITESPACE, " ".into()),
                (CONTINUATION, "\\\n".into()),
                (WHITESPACE, "  ".into()),
                (
                    VALUE,
                    "https://github.com/syncthing/syncthing-gtk/tags".into()
                ),
                (WHITESPACE, " ".into()),
                (VALUE, ".*/v?(\\d\\S+)\\.tar\\.gz".into()),
                (NEWLINE, "\n".into()),
            ]
        );
    }
}
