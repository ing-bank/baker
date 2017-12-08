package com.ing.baker.il

import com.ing.baker.types.RecordField

case class EventType(name: String,
                     ingredientTypes: Seq[RecordField])