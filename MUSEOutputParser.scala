package edu.colorado.hopper
import org.json4s._

import scala.collection.mutable

object MUSEOutputParser {

  case class Alarm(iindex: Int, cg_node_id: Int, bug_type: Int) {
    override def toString = "{\"iindex\" : " + iindex + ", \"cg_node_id\" : " + cg_node_id + ", \"bug_type\" : " + bug_type + "}"
  }

  def main(args: Array[String]): Unit = {
    val alarmStartRegex = """__MUSE_CONSTANT_SEARCH__ Checking alarm {iindex : (\d*), cg_node_id : (\d*), bugType : (\d)}""".r
    val alarmStopRegex = """__MUSE_CONSTANT_SEARCH__ Done checking alarm {iindex : (\d*), cg_node_id : (\d*), bugType : (\d)}""".r

    val results: mutable.Map[Alarm, (Boolean, Set[String])] = mutable.Map.empty[Alarm, (Boolean, Set[String])]
                                                                .withDefaultValue((false,Set()))
    var currentAlarm: Option[Alarm] = None

    for (ln <- io.Source.stdin.getLines if ln contains "__MUSE_CONSTANT_SEARCH__") {
      currentAlarm match {
        case Some(alarm) =>
          alarmStopRegex.findFirstMatchIn(ln) match {
            case Some(regex_match) =>
              if (alarm == Alarm(regex_match.group(1).toInt, regex_match.group(2).toInt, regex_match.group(3).toInt))
                currentAlarm = None
              else
                sys.error("Can't deactivate alarm that isn't active")
            case None =>
              if(ln contains "Search incomplete") {
                results(alarm) = (false, results(alarm)._2)
              } else if (ln contains "Search complete") {
                results(alarm) = (true, results(alarm)._2)
              } else if (ln contains "Constant found:"){
                """{{(.*)}}""".r.findFirstMatchIn(ln) match {
                  case Some(regex_match) =>
                    val curr_result = results(alarm)
                    results(alarm) = (curr_result._1, curr_result._2 + regex_match.group(1))
                  case None => sys.error("Unknown input : " + ln)
                }
              } else if ((ln contains "Bug 5 witnessed") && (alarm.bug_type==4)){
                results(alarm) = (false,Set())
              } else if ((ln contains "Bug 5 refuted") && (alarm.bug_type==4)){
                results(alarm) = (true, Set("1000"))//Not necessarily exactly 1000, but at least 1000, and this will have the same effect in postprocessing
              }
          }
        case None =>
          alarmStartRegex.findFirstMatchIn(ln) match {
            case Some(regex_match) =>
              currentAlarm = Some(Alarm(regex_match.group(1).toInt, regex_match.group(2).toInt, regex_match.group(3).toInt))
            case None =>
              sys.error(s"Can't process input [$ln] without a current alarm")
          }
      }
    }

    require(currentAlarm == None)


    val inputAlarms = org.json4s.native.parseJson(args(0)) \\ "alarms"

    JArray(inputAlarms.filter{inputAlarm =>
      results.exists{ outputAlarm =>
        (inputAlarm \\ "iindex").asInstanceOf[JInt].num.toInt == outputAlarm._1.iindex &&
        (inputAlarm \\ "cg_node_id").asInstanceOf[JInt].num.toInt == outputAlarm._1.cg_node_id &&
        (inputAlarm \\ "bugType").asInstanceOf[JInt].num.toInt == outputAlarm._1.bug_type
      }
    })
  }
}
