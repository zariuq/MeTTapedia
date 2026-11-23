use std::collections::BTreeMap;
use std::fmt;
pub const MAX_CANONICAL_VALUE_NODES: usize = 1_000_000;
pub const MAX_CANONICAL_COLLECTION_ITEMS: usize = 1_000_000;
pub const MAX_CANONICAL_STRING_BYTES: usize = 4 * 1024 * 1024;
pub const MAX_CANONICAL_TOTAL_STRING_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_CANONICAL_BYTE_ARRAY_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_CANONICAL_TOTAL_BYTE_ARRAY_BYTES: usize = 64 * 1024 * 1024;
pub enum RhoValue {
    Map(BTreeMap<String, RhoValue>),
    List(Vec<RhoValue>),
    String(String),
    Bytes(Vec<u8>),
    Integer(i128),
    FloatBits(u64),
    Boolean(bool),
    Nil,
}

impl Clone for RhoValue {
    fn clone(&self) -> Self {
        enum Task<'a> {
            Visit(&'a RhoValue),
            FinishList(usize),
            FinishMap(Vec<&'a str>),
        }

        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(RhoValue::Map(map)) => {
                    let keys: Vec<_> = map.keys().map(String::as_str).collect();
                    tasks.push(Task::FinishMap(keys));
                    tasks.extend(map.values().rev().map(Task::Visit));
                },
                Task::Visit(RhoValue::List(list)) => {
                    tasks.push(Task::FinishList(list.len()));
                    tasks.extend(list.iter().rev().map(Task::Visit));
                },
                Task::Visit(RhoValue::String(value)) => {
                    values.push(RhoValue::String(value.clone()));
                },
                Task::Visit(RhoValue::Bytes(value)) => values.push(RhoValue::Bytes(value.clone())),
                Task::Visit(RhoValue::Integer(value)) => values.push(RhoValue::Integer(*value)),
                Task::Visit(RhoValue::FloatBits(bits)) => values.push(RhoValue::FloatBits(*bits)),
                Task::Visit(RhoValue::Boolean(value)) => values.push(RhoValue::Boolean(*value)),
                Task::Visit(RhoValue::Nil) => values.push(RhoValue::Nil),
                Task::FinishList(length) => {
                    let start = values.len() - length;
                    let children = values.drain(start..).collect();
                    values.push(RhoValue::List(children));
                },
                Task::FinishMap(keys) => {
                    let start = values.len() - keys.len();
                    let children: Vec<_> = values.drain(start..).collect();
                    values.push(RhoValue::Map(
                        keys.into_iter().map(str::to_string).zip(children).collect(),
                    ));
                },
            }
        }
        values
            .pop()
            .expect("RhoValue clone machine produces one value")
    }
}

impl PartialEq for RhoValue {
    fn eq(&self, other: &Self) -> bool {
        let mut work = vec![(self, other)];
        while let Some((left, right)) = work.pop() {
            match (left, right) {
                (RhoValue::Map(left), RhoValue::Map(right)) => {
                    if left.len() != right.len() {
                        return false;
                    }
                    for ((left_key, left_value), (right_key, right_value)) in
                        left.iter().zip(right.iter()).rev()
                    {
                        if left_key != right_key {
                            return false;
                        }
                        work.push((left_value, right_value));
                    }
                },
                (RhoValue::List(left), RhoValue::List(right)) => {
                    if left.len() != right.len() {
                        return false;
                    }
                    work.extend(left.iter().zip(right.iter()).rev());
                },
                (RhoValue::String(left), RhoValue::String(right)) if left == right => {},
                (RhoValue::Bytes(left), RhoValue::Bytes(right)) if left == right => {},
                (RhoValue::Integer(left), RhoValue::Integer(right)) if left == right => {},
                (RhoValue::FloatBits(left), RhoValue::FloatBits(right)) if left == right => {},
                (RhoValue::Boolean(left), RhoValue::Boolean(right)) if left == right => {},
                (RhoValue::Nil, RhoValue::Nil) => {},
                _ => return false,
            }
        }
        true
    }
}

impl Eq for RhoValue {}

impl fmt::Debug for RhoValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Task<'a> {
            Value(&'a RhoValue),
            Key(&'a str),
            Text(&'static str),
        }

        let mut tasks = vec![Task::Value(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Text(text) => formatter.write_str(text)?,
                Task::Key(key) => write!(formatter, "{key:?}")?,
                Task::Value(RhoValue::Map(values)) => {
                    formatter.write_str("Map({")?;
                    tasks.push(Task::Text("})"));
                    for (index, (key, value)) in values.iter().enumerate().rev() {
                        tasks.push(Task::Value(value));
                        tasks.push(Task::Text(": "));
                        tasks.push(Task::Key(key));
                        if index > 0 {
                            tasks.push(Task::Text(", "));
                        }
                    }
                },
                Task::Value(RhoValue::List(values)) => {
                    formatter.write_str("List([")?;
                    tasks.push(Task::Text("])"));
                    for (index, value) in values.iter().enumerate().rev() {
                        tasks.push(Task::Value(value));
                        if index > 0 {
                            tasks.push(Task::Text(", "));
                        }
                    }
                },
                Task::Value(RhoValue::String(value)) => {
                    write!(formatter, "String({value:?})")?;
                },
                Task::Value(RhoValue::Bytes(value)) => {
                    write!(formatter, "Bytes({value:?})")?;
                },
                Task::Value(RhoValue::Integer(value)) => {
                    write!(formatter, "Integer({value:?})")?;
                },
                Task::Value(RhoValue::FloatBits(value)) => {
                    write!(formatter, "FloatBits({value:?})")?;
                },
                Task::Value(RhoValue::Boolean(value)) => {
                    write!(formatter, "Boolean({value:?})")?;
                },
                Task::Value(RhoValue::Nil) => formatter.write_str("Nil")?,
            }
        }
        Ok(())
    }
}

impl Drop for RhoValue {
    fn drop(&mut self) {
        let mut work = Vec::new();
        detach_rho_children(self, &mut work);
        while let Some(mut value) = work.pop() {
            detach_rho_children(&mut value, &mut work);
        }
    }
}

fn detach_rho_children(value: &mut RhoValue, work: &mut Vec<RhoValue>) {
    match value {
        RhoValue::Map(values) => {
            work.extend(std::mem::take(values).into_values());
        },
        RhoValue::List(values) => work.append(values),
        RhoValue::String(_)
        | RhoValue::Bytes(_)
        | RhoValue::Integer(_)
        | RhoValue::FloatBits(_)
        | RhoValue::Boolean(_)
        | RhoValue::Nil => {},
    }
}

pub fn admit_canonical_value(value: &RhoValue) -> Result<(), ValueDecodeError> {
    admit_canonical_value_impl(value, true)
}

fn admit_canonical_value_impl(
    value: &RhoValue,
    enforce_canonical_depth: bool,
) -> Result<(), ValueDecodeError> {
    let mut work = vec![(value, 1usize)];
    let mut nodes = 0usize;
    let mut collection_items = 0usize;
    let mut total_string_bytes = 0usize;
    let mut total_byte_array_bytes = 0usize;
    while let Some((value, depth)) = work.pop() {
        nodes = nodes
            .checked_add(1)
            .ok_or_else(|| ValueDecodeError::new("$", "canonical value node count overflowed"))?;
        if nodes > MAX_CANONICAL_VALUE_NODES {
            return Err(ValueDecodeError::new(
                "$",
                format!("canonical value exceeds {MAX_CANONICAL_VALUE_NODES} nodes"),
            ));
        }
        if enforce_canonical_depth && depth > crate::parse::MAX_DDL_STRUCTURAL_DEPTH {
            return Err(ValueDecodeError::new(
                "$",
                format!(
                    "canonical value nesting exceeds {}",
                    crate::parse::MAX_DDL_STRUCTURAL_DEPTH
                ),
            ));
        }
        match value {
            RhoValue::Map(values) => {
                collection_items = collection_items.checked_add(values.len()).ok_or_else(|| {
                    ValueDecodeError::new("$", "canonical collection item count overflowed")
                })?;
                let child_depth = depth.checked_add(1).ok_or_else(|| {
                    ValueDecodeError::new("$", "canonical value depth overflowed")
                })?;
                for (key, value) in values.iter().rev() {
                    account_canonical_string(key, &mut total_string_bytes)?;
                    work.push((value, child_depth));
                }
            },
            RhoValue::List(values) => {
                collection_items = collection_items.checked_add(values.len()).ok_or_else(|| {
                    ValueDecodeError::new("$", "canonical collection item count overflowed")
                })?;
                let child_depth = depth.checked_add(1).ok_or_else(|| {
                    ValueDecodeError::new("$", "canonical value depth overflowed")
                })?;
                work.extend(values.iter().rev().map(|value| (value, child_depth)));
            },
            RhoValue::String(value) => {
                account_canonical_string(value, &mut total_string_bytes)?;
            },
            RhoValue::Bytes(value) => {
                account_canonical_bytes(value, &mut total_byte_array_bytes)?;
            },
            RhoValue::Integer(_)
            | RhoValue::FloatBits(_)
            | RhoValue::Boolean(_)
            | RhoValue::Nil => {},
        }
        if collection_items > MAX_CANONICAL_COLLECTION_ITEMS {
            return Err(ValueDecodeError::new(
                "$",
                format!(
                    "canonical value exceeds {MAX_CANONICAL_COLLECTION_ITEMS} collection items"
                ),
            ));
        }
    }
    Ok(())
}

fn account_canonical_bytes(
    value: &[u8],
    total_byte_array_bytes: &mut usize,
) -> Result<(), ValueDecodeError> {
    if value.len() > MAX_CANONICAL_BYTE_ARRAY_BYTES {
        return Err(ValueDecodeError::new(
            "$",
            format!("canonical byte array exceeds {MAX_CANONICAL_BYTE_ARRAY_BYTES} bytes"),
        ));
    }
    *total_byte_array_bytes = total_byte_array_bytes
        .checked_add(value.len())
        .ok_or_else(|| {
            ValueDecodeError::new("$", "canonical total byte-array byte count overflowed")
        })?;
    if *total_byte_array_bytes > MAX_CANONICAL_TOTAL_BYTE_ARRAY_BYTES {
        return Err(ValueDecodeError::new(
            "$",
            format!(
                "canonical byte arrays exceed {MAX_CANONICAL_TOTAL_BYTE_ARRAY_BYTES} total bytes"
            ),
        ));
    }
    Ok(())
}

pub(crate) fn account_canonical_string(
    value: &str,
    total_string_bytes: &mut usize,
) -> Result<(), ValueDecodeError> {
    if value.len() > MAX_CANONICAL_STRING_BYTES {
        return Err(ValueDecodeError::new(
            "$",
            format!("canonical string exceeds {MAX_CANONICAL_STRING_BYTES} bytes"),
        ));
    }
    *total_string_bytes = total_string_bytes.checked_add(value.len()).ok_or_else(|| {
        ValueDecodeError::new("$", "canonical total string byte count overflowed")
    })?;
    if *total_string_bytes > MAX_CANONICAL_TOTAL_STRING_BYTES {
        return Err(ValueDecodeError::new(
            "$",
            format!("canonical strings exceed {MAX_CANONICAL_TOTAL_STRING_BYTES} total bytes"),
        ));
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueDecodeError {
    pub path: String,
    pub message: String,
}

impl ValueDecodeError {
    pub(crate) fn new(path: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for ValueDecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.path, self.message)
    }
}
