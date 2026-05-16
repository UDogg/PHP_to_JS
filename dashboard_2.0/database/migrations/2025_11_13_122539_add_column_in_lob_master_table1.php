<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::table('lob_master', function (Blueprint $table) {
            if (!Schema::hasColumn('lob_master', 'lob_order_by')) {
                $table->string('lob_order_by')->nullable();
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('lob_master', function (Blueprint $table) {
            if (Schema::hasColumn('lob_master', 'lob_order_by')) {
                $table->dropColumn('lob_order_by');
            }
        });
    }
};
