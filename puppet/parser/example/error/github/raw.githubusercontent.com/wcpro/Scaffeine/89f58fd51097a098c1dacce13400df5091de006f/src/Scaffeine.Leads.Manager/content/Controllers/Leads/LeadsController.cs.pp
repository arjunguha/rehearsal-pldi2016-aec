namespace $rootnamespace$.Controllers.Leads
{
    using System.Web.Mvc;

    using $rootnamespace$.Core.Interfaces.Service;
    using $rootnamespace$.Core.Model;

    public partial class LeadsController : Controller
    {
        private readonly ILeadService _service;

        public LeadsController(ILeadService service)
        {
            this.Service = _service = service;
        }

        public ActionResult Record(int id)
        {
            var lead = _service.GetById(id);
            return this.View(lead);
        }

		public ActionResult Manager(int page = 1, int size = 20)
		{
		    var leads = _service.Page(page, size);
		    return this.View(leads);
		}

        [HttpPost]
        public ActionResult Delete(int id)
        {
            var entity = _service.GetById(id);
            _service.Delete(entity);

            TempData["Success"] = "Lead was successfuly deleted";

            return RedirectToAction("Manager");
        }
    }
}