namespace $rootnamespace$.Areas.Api.Controllers
{
    using System.Collections;
    using System.Linq;
    using System.Web.Http;

    public partial class DepartmentsController
    {
        [HttpGet]
        public IEnumerable List()
        {
            var departments = Service.GetAll().OrderBy(d => d.Name).ToList();

            return departments.Select(d => new
                                               {
                                                   d.Id,
                                                   d.RowVersion,
                                                   d.Created,
                                                   d.Updated,
                                                   d.Name,
                                                   d.Description,
                                                   Categories = d.Categories.Select(c => new
                                                                                             {
                                                                                                 c.Id,
                                                                                                 c.RowVersion,
                                                                                                 c.Created,
                                                                                                 c.Updated,
                                                                                                 c.Name,
                                                                                                 c.Description,                                
                                                                                                 c.DepartmentId
                                                                                             })
                                               });
        }
    }
}
