structure StringOrdKey = struct
type ord_key = string
val compare = String.compare
end
                           
structure StringBinaryMap = BinaryMapFn (StringOrdKey)
structure StringListMap = ListMapFn (StringOrdKey)
structure StringBinarySet = BinarySetFn (StringOrdKey)
structure StringListSet = ListSetFn (StringOrdKey)

