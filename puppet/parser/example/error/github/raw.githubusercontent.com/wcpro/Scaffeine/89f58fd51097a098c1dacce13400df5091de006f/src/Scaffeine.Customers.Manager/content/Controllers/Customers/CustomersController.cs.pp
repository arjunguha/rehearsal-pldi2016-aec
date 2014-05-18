namespace $rootnamespace$.Controllers.Customers
{
    using System.Web.Mvc;

    using $rootnamespace$.Core.Interfaces.Service;
    using $rootnamespace$.Core.Model;

    public class CustomersController : Controller
    {
         private readonly ICustomerService _service;

        public CustomersController(ICustomerService service)
        {
            this.Service = _service = service;
        }

        public ActionResult Record(int id)
        {
            var customer = _service.GetById(id);
            return this.View(customer);
        }

		public ActionResult Manager(int page = 1, int size = 20)
		{
		    var Customers = _service.Page(page, size);
		    return this.View(Customers);
		}

        [HttpPost]
        public ActionResult Delete(int id)
        {
            var entity = _service.GetById(id);
            _service.Delete(entity);

            TempData["Success"] = "Customer was successfuly deleted";

            return RedirectToAction("Manager");
        }
    }
}
