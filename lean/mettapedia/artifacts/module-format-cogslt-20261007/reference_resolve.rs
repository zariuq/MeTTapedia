use std::fmt;
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ModuleRef {
    Registry(String),
    File(String),
}

impl ModuleRef {
    pub fn parse(value: &str) -> Result<Self, ResolveError> {
        if let Some(name) = value.strip_prefix("rho:") {
            if name.is_empty() {
                return Err(ResolveError::InvalidReference(value.to_string()));
            }
            return Ok(Self::Registry(format!("rho:{name}")));
        }
        if let Some(path) = value.strip_prefix("file:") {
            if path.is_empty() {
                return Err(ResolveError::InvalidReference(value.to_string()));
            }
            return Ok(Self::File(path.to_string()));
        }
        if value.contains(':') {
            return Err(ResolveError::UnsupportedScheme(value.to_string()));
        }
        if value.is_empty() {
            return Err(ResolveError::InvalidReference(value.to_string()));
        }
        Ok(Self::File(value.to_string()))
    }

    pub fn external_form(&self) -> String {
        match self {
            Self::Registry(uri) => uri.clone(),
            Self::File(path) => format!("file:{path}"),
        }
    }
}

impl fmt::Display for ModuleRef {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.external_form())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolveError {
    InvalidReference(String),
    UnsupportedScheme(String),
    NotFound(ModuleRef),
    Registry(String),
    FileIoUnavailable { reference: ModuleRef },
    IntegrityMismatch { reference: ModuleRef },
    LimitExceeded { resource: &'static str, limit: usize },
}

impl fmt::Display for ResolveError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidReference(value) => {
                write!(formatter, "invalid module reference `{value}`")
            },
            Self::UnsupportedScheme(value) => {
                write!(formatter, "unsupported module scheme in `{value}`")
            },
            Self::NotFound(reference) => write!(formatter, "module `{reference}` was not found"),
            Self::Registry(message) => {
                write!(formatter, "Rholang registry lookup failed: {message}")
            },
            Self::FileIoUnavailable { reference } => write!(
                formatter,
                "module `{reference}` requires the future Rholang File I/O capability"
            ),
            Self::IntegrityMismatch { reference } => {
                write!(formatter, "content commitment mismatch for module `{reference}`")
            },
            Self::LimitExceeded { resource, limit } => {
                write!(formatter, "module {resource} limit exceeded (maximum {limit})")
            },
        }
    }
}
