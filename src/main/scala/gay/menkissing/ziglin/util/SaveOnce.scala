package gay.menkissing.ziglin.util

class SaveOnce[A]:
  private var data: Option[A] = None
  
  def getOrInit(initValue: => A): A =
    data match
      case Some(v) => v
      case None =>
        val res = initValue
        data = Some(res)
        res
