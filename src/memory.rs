// #![warn(missing_docs)]

//! TODO

use thiserror::Error;

/// Todos os erros possíveis associados a uma memória.
#[derive(Error, Debug)]
pub enum MemoryError {
    /// Ocorre quando há uma tentativa de acesso a um endereço fora dos limites da memória.
    #[error("Ocorreu uma tentativa de acesso fora dos limites da memória [Address: {0}]")]
    OutOfBounds(usize),
}

/// *Trait* que caracteriza as funções básicas de uma memória.
pub trait Memory {
    /// Retorna uma referência do valor armazenado no endereço `address`.
    ///
    /// # Errors
    ///
    /// Essa função irá retornar um erro caso o endereço especificado seja inválido.
    fn get(&self, address: usize) -> Result<&usize, MemoryError>;

    /// Retorna uma referência ***mutável*** do valor armazenado no endereço `address`.
    ///
    /// # Errors
    ///
    /// Essa função irá retornar um erro caso o endereço especificado seja inválido.
    fn get_mut(&mut self, address: usize) -> Result<&mut usize, MemoryError>;

    /// Altera o valor amazenado no endereço `address` para o valor `value` e retorna o valor
    /// antigo armazenado.
    ///
    /// # Errors
    ///
    /// Essa função irá retornar um erro caso o endereço especificado seja inválido.
    fn set(&mut self, address: usize, value: usize) -> Result<usize, MemoryError>;
}

pub const RAM_SIZE: usize = 32_768;

pub struct RAM {
    memory: Vec<usize>,
}

impl Memory for RAM {
    fn get(&self, address: usize) -> Result<&usize, MemoryError> {
        self.memory
            .get(address)
            .ok_or_else(|| MemoryError::OutOfBounds(address))
    }

    fn get_mut(&mut self, address: usize) -> Result<&mut usize, MemoryError> {
        self.memory
            .get_mut(address)
            .ok_or_else(|| MemoryError::OutOfBounds(address))
    }

    fn set(&mut self, address: usize, value: usize) -> Result<usize, MemoryError> {
        let old = self.get_mut(address)?;
        let ret = *old;
        *old = value;
        Ok(ret)
    }
}

impl Default for RAM {
    fn default() -> Self {
        Self {
            memory: vec![0; RAM_SIZE],
        }
    }
}

impl RAM {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            memory: vec![0; capacity],
        }
    }
}

#[cfg(test)]
mod tests {}
