This is a comparison of Baker with similar solutions. Feedback and contributions to solutions not listed are most welcome.
 
| Feature | Baker | [Camunda](https://camunda.com/) | [Pega](https://www.pega.com/) | [Netflix Conductor](https://netflix.github.io/conductor/) | [Uber Cadence](https://github.com/uber/cadence) | [Apache Airflow](https://airflow.apache.org/) |
| --- | --- | --- | --- | --- | --- | --- |
| Owned By | ING | Camunda | PEGA Systems | Netflix | Uber | Community |
| Primary Purpose | Orchestration of (micro-)services | Process Automation | Workflow or case management | Orchestration of (micro-)services | Orchestration of long-running business logic | Workflow of big-data pipelines |
| Typical Use | Straight Through Processing (STP) | Business Processes with Decision Making | Business Processes with Decision Making | STP | STP | Big data |
| Skill-set required | Java or Scala | Java, Business Process Modelling Notation (BPMN) | Pega-specific | JSON | Java | Python, Bash |
| Execution Model | Petri-net | BPMN for workflows, Decision Model and Notation (DMN) for business rules | Don’t know | Queueing Theory | Queueing Theory | Graph Theory |
| In-memory processing | Yes | Yes | No | Yes | No | No |
| Data Persistence | Event sourcing with Cassandra |Relational DB via JDBC | Relational | Dedicated Storage (Dynomite) | Cassandra | N/A |
| Process Visualization | [Graphviz](https://www.graphviz.org/) | Based on BPMN | Based on BPMN | Dedicated UI | No | Dedicated UI |
| License Model | Open-source | Community Platform is open-source | Pay per Case | Open-source | Open-source |Open-source |
| Rich UI | No | Yes | Yes | Yes | No | Yes |

