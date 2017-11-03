package com.ing.baker.il

import com.ing.baker.il.types.RecordField

case class EventType(name: String,
                     ingredientTypes: Seq[RecordField])