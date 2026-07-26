// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[derive(Clone, Debug)]
pub struct GeneratedProgram {
    pub function_name: &'static str,
    pub target_name: &'static str,
    pub description: &'static str,
    pub source: String,
}

#[derive(Debug)]
pub(crate) struct FunctionSpec {
    pub params: Vec<String>,
    pub requires: Vec<String>,
    pub ensures: Vec<String>,
    pub return_ty: &'static str,
    pub body: &'static str,
}

impl FunctionSpec {
    pub(crate) fn render(
        self,
        target_name: &'static str,
        description: &'static str,
    ) -> GeneratedProgram {
        let function_name = "fuzz_case";
        let mut source = String::from("#[trust_vc::proof]\n");
        for require in self.requires {
            source.push_str(&format!("#[trust_vc::requires({require})]\n"));
        }
        for ensure in self.ensures {
            source.push_str(&format!("#[trust_vc::ensures({ensure})]\n"));
        }
        source.push_str(&format!(
            "fn {function_name}({}) -> {} {{\n    {}\n}}\n",
            self.params.join(", "),
            self.return_ty,
            self.body
        ));

        GeneratedProgram {
            function_name,
            target_name,
            description,
            source,
        }
    }
}

#[derive(Debug)]
pub(crate) struct ByteStream<'a> {
    data: &'a [u8],
    cursor: usize,
}

impl<'a> ByteStream<'a> {
    pub(crate) fn new(data: &'a [u8]) -> Self {
        Self { data, cursor: 0 }
    }

    fn next_byte(&mut self) -> u8 {
        let value = self.data.get(self.cursor).copied().unwrap_or(0);
        self.cursor += 1;
        value
    }

    pub(crate) fn choose_index(&mut self, len: usize) -> usize {
        if len == 0 {
            0
        } else {
            usize::from(self.next_byte()) % len
        }
    }

    pub(crate) fn choose<'b, T>(&mut self, choices: &'b [T]) -> &'b T {
        &choices[self.choose_index(choices.len())]
    }

    pub(crate) fn flag(&mut self) -> bool {
        self.next_byte() & 1 == 1
    }

    pub(crate) fn small_u64(&mut self, max_inclusive: u64) -> u64 {
        if max_inclusive == 0 {
            0
        } else {
            u64::from(self.next_byte()) % (max_inclusive + 1)
        }
    }

    pub(crate) fn small_i32(&mut self, min: i32, max: i32) -> i32 {
        assert!(min <= max, "invalid i32 range");
        let span = u32::try_from(max - min + 1).expect("range span should fit in u32");
        min + i32::try_from(u32::from(self.next_byte()) % span).expect("offset should fit in i32")
    }
}
