package com.ing.baker.types

case class ComplexPOJOExample(simplePOJOExample: SimplePOJOExample,
                              string: String,
                              boolean: Boolean,
                              upperboundRecord : List[_ <: SimplePOJOExample]) {
}
