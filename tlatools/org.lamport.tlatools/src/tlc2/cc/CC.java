package tlc2.cc;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.lang.reflect.Array;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import tlc2.cc.CCAction.Type;
import tlc2.tool.Action;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.impl.CCTool;
import tlc2.value.IValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.SetDiffValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.Value;
import util.DebugPrinter;
import util.FilenameToStream;
import util.ToolIO;
import util.UniqueString;


/**
 * A Rounds is a sequence of Round and a Round is a sequence of action.
 * TLCState should be generated by the ordered Rounds' actions.
 */
public class CC  {
	private static Rounds rounds = new Rounds();
	private static UniqueString msgs = null;
	public static ActionMap actionMap = null;
	enum MsgsType {SET, FCN};
	private static MsgsType msgsType = MsgsType.SET;
	public static boolean cleanChannel = false;
	
	public static Action[] actions;
	public static HashMap<Integer, Action> id2Action = new HashMap<>();
	public static String RE_Meta_Msg = "@Msg\\.(\\w+)=(\\w+)";
	
	public static long cnt = 0;
	
	public static void init(CCTool tool, String roundsFile) {
		System.out.println("Initialize CC.");
		
		actions = tool.getActions();
		for(int i=0;i<actions.length;i++) {
			id2Action.put(actions[i].getId(), actions[i]);
		}
		printActions();
		
		System.out.println("construct Rounds");
		if(!constructRounds(roundsFile)) {
			System.exit(1);
		}
		print();
		initializeNextActions();
		
//		print();
		printNexts();
	}
	public static void setEmpty() {
		TLCStateMutCC.setCCEmpty();
	}
	
	public static void printActions() {
		for(int i=0;i<actions.length;i++) {
			System.out.println("action " + actions[i].getId() + " : " + actions[i].getName() + " " + actions[i].con);
		}
	}
	
	public static void printError(String msg) {
		ToolIO.out.println(msg);
		System.exit(-1);
	}
	
	
	private static boolean constructRounds(String roundsFile) {
//		initRaftRound();
//		initBasicPaxosRound();
		CC.actionMap = new ActionMap();
		CC.actionMap.fill();
		
		Pattern meta_pattern = Pattern.compile(RE_Meta_Msg);
		
		try (BufferedReader reader = new BufferedReader(new FileReader(roundsFile))) {
      String line;
      while ((line = reader.readLine()) != null) {
      	line = line.replaceAll("\\s", "");
      	if(line.startsWith("@")) {

      		Matcher matcher = meta_pattern.matcher(line);
      		if(matcher.find()){
      			int cnt = matcher.groupCount();
      			if(cnt==2) {
      				String k = matcher.group(1);
      				String v = matcher.group(2);
      				if(k.equals("Type")) {
      					if(v.equals("Set")) {
      						CC.msgsType = MsgsType.SET;
      					} else if(v.equals("Fcn")) {
      						CC.msgsType = MsgsType.FCN;
      					} else {
      						printError("Message type should be Set or Fcn");
      						return false;
      					}
      				} else if(k.equals("Var")) {
      					CC.msgs = UniqueString.internTbl.find(v);
      					if(CC.msgs == null) {
      						printError("No such variable: " + v);
      						return false;
      					}
      				} else if(k.equals("CleanChannel")){
      					if(v.equals("FALSE")) {
      						CC.cleanChannel = false;
      					} else if(v.equals("TRUE")) {
      						CC.cleanChannel = true;
      					} else {
      						printError("CleanChannel should be FALSE or TRUE");
      						return false;
      					}
      					
      				} else {
      					printError("Syntax error: " + line);
          			return false;
      				}
      			}else {
      				printError("Syntax error: " + line);
        			return false;
      			}
      		} else {
      			printError("Syntax error: " + line);
      			return false;
      		}
      		
      	} else {
      		rounds.addRound(line);
      	}
        
      }
    } catch (IOException e) {
      e.printStackTrace();
    }
		return true;
	}
	
	private static void initBasicPaxosRound() {
		CC.msgs = UniqueString.uniqueStringOf("msgs");
		CC.msgsType = MsgsType.SET;
		rounds.addRound("prepare0", new int[] { 1 }, new int[] { 7, 9, 11 });
		rounds.addRound("ack0", 		null, new int[] { 2, 3});
		rounds.addRound("propose0", null, new int[] { 8, 10, 12 });
		rounds.addRound("prepare1", 		new int[] { 4 }, new int[] { 7, 9, 11 });
		rounds.addRound("ack1", null, new int[] { 5,6 });
		rounds.addRound("propose1", null, new int[] { 8,10,12 });
	}
	private static void initRaftRound() {
		CC.msgs = UniqueString.uniqueStringOf("messages");
		CC.msgsType = MsgsType.FCN;
		rounds.addRound("Timeout1", new int[] { 1 }, null);
		rounds.addRound("Vote1", new int[] {4,7,10}, new int[] {13,14,15});
		rounds.addRound("HandleVoteResponse1", null , new int[] {22,25,28});
		rounds.addRound("BecomeLeader1", new int[] {31} , null);

		rounds.addRound("ClientRequest1-v1", new int[] {34} , null);
		rounds.addRound("Append1", new int[] {43,46} , new int[] {50,51});
		rounds.addRound("HandleAppendResponse1" , null, new int[] {61,64});
		rounds.addRound("Commit1" , new int[] {67}, null);
		
		rounds.addRound("ClientRequest1-v2", new int[] {37} , null);
		rounds.addRound("Append1", new int[] {43,46} , new int[] {50,51});
		rounds.addRound("HandleAppendResponse1" , null, new int[] {61,64});
		rounds.addRound("Commit1" , new int[] {67}, null);
	}
	private static void inittmpRound() {
		CC.msgs = UniqueString.uniqueStringOf("msgs");
		CC.msgsType = MsgsType.FCN;
		rounds.addRound("round0", null, new int[] { 1 });
		rounds.addRound("round1", null, new int[] { 1 });
		rounds.addRound("round2", null, new int[] { 1 });
		rounds.addRound("round3", null, new int[] { 1 });
		rounds.addRound("round4", null, new int[] { 1 });
	}
	
	public static Round getRound(int id) {
		return rounds.getRound(id);
	}
	public static int firstRoundId() {
		return rounds.firstRoundId();
	}
	
	public static CCAction[] getNextActions(CCAction pre){
		ArrayList<CCAction> ret = new ArrayList<>();
		
		switch(pre.getType()) {
		case Init:{
			// add first send
			CCAction a = rounds.getNext(pre);
			if(a.getType() == Type.Send) {
				ret.add(rounds.getNext(pre));
			}else {
				Round cur = rounds.getFirstRound();
				ret.addAll(cur.getAllRcvs());
				CCAction nextSend = rounds.getNextSend(cur.getRoundNumber());
				if(nextSend != null) {
					ret.add(nextSend);
				}
			}
			
			break;
		}
		case Send:{
			Round cur = rounds.getRound(pre.getRoundNumber());
			if(!cur.isLastSend(pre)) {
				ret.add(cur.getNext(pre));
				break;
			}
			// last send, add all rcvs
			if(cur.hasRcv()) {
				ret.addAll(cur.getNexts(pre));
			}
			// all msgs lost, add next send
			CCAction nextSend = rounds.getNextSend(pre.getRoundNumber());
			if(nextSend != null) {
				ret.add(nextSend);
			}
			break;
		}
		case Rcv: {
			Round cur = rounds.getRound(pre.getRoundNumber());
			ret.addAll(cur.getNexts(pre));
			Round next = rounds.getRound(pre.getRoundNumber()+1);
			if(next == null) {
				break;
			}
			if(next.hasSend()) {
				ret.add(next.getFirstAction());
			}else {
				ret.addAll(next.getAllRcvs());
				CCAction nextSend = rounds.getNextSend(pre.getRoundNumber()+1);
				if(nextSend != null) {
					ret.add(nextSend);
				}
			}
			break;
		}
		default:{ break;}
		}
		return ret.toArray(new CCAction[0]);
	}
	
	private static void initializeNextActions() {
		CCAction cur = CCAction.Empty;
		while(cur != null) {
			cur.setNexts(CC.getNextActions(cur));
			cur = rounds.getNext(cur);
		}
	}
	
	public static UniqueString getMsgs() {
		return msgs;
	}
	public static void print() {
		rounds.print();
		
	}
	public static void printNexts() {
		rounds.printNexts();
	}
	public static IValue getBeginRoundMsgs(TLCState state) {
		CCState ccstate = ((TLCStateMutCC)state).getCCState();
		if(ccstate.getPre().getType() == Type.Init) {
			return state.lookup(CC.getMsgs());
		}
		if(ccstate.getMsgs2() == null) {
			return state.lookup(CC.getMsgs());
		}
		switch(msgsType) {
		case SET:{
			return new SetDiffValue((Value)state.lookup(CC.getMsgs()), (Value)ccstate.getMsgs2());
		}
		case FCN:{
			return FcnUtil.diff((Value)state.lookup(CC.getMsgs()),(Value)ccstate.getMsgs2());
		}
		default:{
			return null;
		}
		}
	}
	public static IValue getEmptyMsgs(TLCState state) {
		switch(msgsType) {
		case SET:{
			return new SetEnumValue();
		}
		case FCN:{
			return new FcnRcdValue(new Value[0], new Value[0], true);
		}
		default:{
			CC.printError("Unsupported channel type!");
			return null;
		}
		}
	}
}


