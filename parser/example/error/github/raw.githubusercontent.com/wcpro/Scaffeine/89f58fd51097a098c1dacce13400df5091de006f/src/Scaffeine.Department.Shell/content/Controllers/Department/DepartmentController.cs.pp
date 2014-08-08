namespace $rootnamespace$.Controllers.Department
{
    using System.Web.Mvc;
    using Core.Interfaces.Service;

    public class DepartmentController : Controller
    {
        protected IDepartmentService DepartmentService;
        public DepartmentController(IDepartmentService service)
        {
            DepartmentService = service;
        }

        public ActionResult Categories()
        {
            return View();
        }
    }
}
