package tlc2.cc;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import tlc2.tool.Action;

public class ActionMap {
	// action name -> actions with different args
	public HashMap<String, List<Action>> name2list;
	
    // fill name2list
	public void fill() {
		Action[] actions = CC.actions;
		for (Action action : actions) {
			String name = action.getNameOfDefault();
			if(name2list.containsKey(name)) {
				name2list.put(name, new ArrayList<>());
			}
			name2list.get(name).add(action);
		}
	}
	public List<Action> get(String name){
		return name2list.get(name);
	}
}
