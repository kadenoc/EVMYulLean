namespace ffi

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

def SHA256 (d : ByteArray) : Except String ByteArray :=
  pure <| sha256 d d.size.toUSize

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213                    then throw "error"
  if d[212]! ∉ [0, 1].map Nat.toUInt8 then throw "error"
  return BLAKE2Compress d

@[extern "memset_zero"]
def memsetZero (n : USize) : ByteArray := ⟨⟨List.replicate n.toNat 0⟩⟩

def ByteArray.zeroesImpl (n : Nat) : ByteArray := memsetZero n.toUSize

/--
`n` zero bytes. The reference body is kernel-reducible (so proofs about
byte-array reads/pads can proceed by `rfl`/`decide`); at runtime it is
implemented by the C `memset_zero` via `zeroesImpl`.
-/
@[implemented_by ByteArray.zeroesImpl]
def ByteArray.zeroes (n : Nat) : ByteArray := ⟨⟨List.replicate n 0⟩⟩

@[extern "keccak256"]
opaque keccak256 (input : @& ByteArray) (len : USize) : ByteArray

def KECCAK256 (d : ByteArray) : Except String ByteArray :=
  pure <| keccak256 d d.size.toUSize

def KEC (data : ByteArray) : ByteArray :=
  ffi.KECCAK256 data |>.toOption.getD .empty

end ffi
