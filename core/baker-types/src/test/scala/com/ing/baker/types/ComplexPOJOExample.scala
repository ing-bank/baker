package com.ing.baker.types

case class ComplexPOJOExample(simplePOJOExample: SimplePOJOExample,
                              string: String,
                              boolean: Boolean) {
}

case class RecursiveType(a: String,
                         b: Option[RecursiveType])